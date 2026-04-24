from __future__ import annotations

from fastapi.testclient import TestClient

import api.analyze as analyze_api
import lib.abi_parser as abi_parser


class FakeRecord:
    def __init__(self, *, record_id: str, sequence: bytes, quality: list[int]):
        self.id = record_id
        self.seq = "FALLBACKSEQ"
        self.annotations = {"abif_raw": {"PBAS2": sequence, "PCON2": quality}}


client = TestClient(analyze_api.app)


def test_api_health_endpoint() -> None:
    response = client.get("/api/health")
    assert response.status_code == 200
    assert response.json() == {"status": "ok"}


def test_analyze_e2e_uses_real_pipeline_except_file_decoder(monkeypatch) -> None:
    sequence = b"AAAACGCCTCCCTTTTGGACAAGGGGTAAGCTGGAGAAAA"
    quality = [40] * len(sequence)

    monkeypatch.setattr(
        abi_parser.SeqIO,
        "read",
        lambda *_args, **_kwargs: FakeRecord(record_id="e2e-record", sequence=sequence, quality=quality),
    )

    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"ABIFsimulated", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )

    payload = response.json()
    assert response.status_code == 200
    assert payload["ok"] is True
    assert payload["analysis"]["primer_type"] == "T0128"
    assert payload["qc"]["sequence_length"] == len(sequence)
    assert payload["report"]["mutation_summary"]["total_mutations"] >= 1


def test_analyze_maps_detector_value_error_to_invalid_primer(monkeypatch) -> None:
    parsed = {
        "record_id": "demo-record",
        "sequence": "ACGT",
        "quality": [40, 40, 40, 40],
        "length": 4,
        "warnings": [],
    }

    monkeypatch.setattr(analyze_api, "parse_ab1", lambda _: parsed)
    monkeypatch.setattr(analyze_api, "detect_mutations", lambda *_args, **_kwargs: (_ for _ in ()).throw(ValueError("x")))

    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"ABIFfake", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )

    assert response.status_code == 400
    assert response.json()["error"]["code"] == "INVALID_PRIMER_TYPE"


def test_analyze_maps_unexpected_exception_to_analysis_error(monkeypatch) -> None:
    parsed = {
        "record_id": "demo-record",
        "sequence": "ACGT",
        "quality": [40, 40, 40, 40],
        "length": 4,
        "warnings": [],
    }

    monkeypatch.setattr(analyze_api, "parse_ab1", lambda _: parsed)
    monkeypatch.setattr(analyze_api, "generate_report", lambda *_args, **_kwargs: (_ for _ in ()).throw(RuntimeError("x")))

    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"ABIFfake", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )

    assert response.status_code == 500
    assert response.json()["error"]["code"] == "ANALYSIS_ERROR"
