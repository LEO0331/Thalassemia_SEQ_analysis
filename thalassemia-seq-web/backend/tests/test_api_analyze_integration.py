from __future__ import annotations

from fastapi.testclient import TestClient

import api.analyze as analyze_api


client = TestClient(analyze_api.app)


def test_analyze_missing_file_returns_error() -> None:
    response = client.post("/api/analyze", data={"primer_type": "T0128"})
    payload = response.json()
    assert response.status_code == 400
    assert payload["error"]["code"] == "MISSING_FILE"


def test_analyze_invalid_file_type_returns_error() -> None:
    response = client.post(
        "/api/analyze",
        files={"file": ("sample.txt", b"abcd", "text/plain")},
        data={"primer_type": "T0128"},
    )
    payload = response.json()

    assert response.status_code == 400
    assert payload["ok"] is False
    assert payload["error"]["code"] == "INVALID_FILE_TYPE"


def test_analyze_invalid_primer_returns_error() -> None:
    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"fake-ab1", "application/octet-stream")},
        data={"primer_type": "T9999"},
    )
    payload = response.json()

    assert response.status_code == 400
    assert payload["error"]["code"] == "INVALID_PRIMER_TYPE"


def test_analyze_file_too_large_returns_error(monkeypatch) -> None:
    data = b"A" * (analyze_api.MAX_FILE_SIZE_BYTES + 1)
    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", data, "application/octet-stream")},
        data={"primer_type": "T0128"},
    )
    payload = response.json()

    assert response.status_code == 413
    assert payload["error"]["code"] == "FILE_TOO_LARGE"


def test_analyze_abi_parse_error_returns_expected_code(monkeypatch) -> None:
    def fake_parse_ab1(_: bytes):
        raise ValueError("bad abi")

    monkeypatch.setattr(analyze_api, "parse_ab1", fake_parse_ab1)

    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"ABIF-fake-ab1", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )
    payload = response.json()

    assert response.status_code == 400
    assert payload["error"]["code"] == "ABI_PARSE_ERROR"


def test_analyze_success_with_mocked_pipeline(monkeypatch) -> None:
    parsed = {
        "record_id": "demo-record",
        "sequence": "ACGT",
        "quality": [40, 40, 40, 40],
        "length": 4,
        "warnings": [],
    }
    qc = {
        "sequence_length": 4,
        "average_quality": 40.0,
        "low_quality_regions": [],
        "warnings": [],
    }
    analysis = {
        "primer_type": "T0128",
        "sequence_length": 4,
        "mutations": [],
        "warnings": [],
    }
    report = {
        "file_name": "sample.ab1",
        "primer_type": "T0128",
        "sequence_length": 4,
        "qc_summary": qc,
        "mutation_summary": {"total_mutations": 0, "status_counts": {}, "mutations": []},
        "warnings": [],
        "disclaimer": "test",
    }

    monkeypatch.setattr(analyze_api, "parse_ab1", lambda _: parsed)
    monkeypatch.setattr(analyze_api, "assess_quality", lambda sequence, quality: qc)
    monkeypatch.setattr(analyze_api, "detect_mutations", lambda sequence, quality, primer_type: analysis)
    monkeypatch.setattr(
        analyze_api,
        "generate_report",
        lambda file_name, primer_type, parsed_payload, qc_payload, analysis_payload: report,
    )

    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"ABIF-fake-ab1", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )
    payload = response.json()

    assert response.status_code == 200
    assert payload["ok"] is True
    assert payload["file_name"] == "sample.ab1"
    assert payload["primer_type"] == "T0128"
    assert payload["qc"]["sequence_length"] == 4
    assert "report" in payload


def test_analyze_abif_magic_validation_rejects_spoofed_extension() -> None:
    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"NOTABIF", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )
    payload = response.json()

    assert response.status_code == 400
    assert payload["error"]["code"] == "INVALID_FILE_TYPE"


def test_analyze_rejects_empty_file() -> None:
    response = client.post(
        "/api/analyze",
        files={"file": ("sample.ab1", b"", "application/octet-stream")},
        data={"primer_type": "T0128"},
    )
    payload = response.json()

    assert response.status_code == 400
    assert payload["error"]["code"] == "INVALID_FILE_TYPE"
