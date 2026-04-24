from __future__ import annotations

import pytest

import lib.abi_parser as abi_parser


class FakeRecord:
    def __init__(self, *, record_id: str, annotations: dict, seq: str):
        self.id = record_id
        self.annotations = annotations
        self.seq = seq


def test_normalize_sequence_and_quality_variants() -> None:
    assert abi_parser._normalize_sequence(b"ACGT") == "ACGT"
    assert abi_parser._normalize_sequence(["A", "C", "G"]) == "ACG"
    assert abi_parser._normalize_sequence(123) == "123"

    assert abi_parser._normalize_quality(b"ABC") == [65, 66, 67]
    assert abi_parser._normalize_quality("AZ") == [65, 90]
    assert abi_parser._normalize_quality([1, "B", "9", object()])[:3] == [1, 66, 57]
    assert abi_parser._normalize_quality(None) == []


def test_parse_ab1_uses_abif_raw_fields(monkeypatch: pytest.MonkeyPatch) -> None:
    record = FakeRecord(
        record_id="rec-1",
        annotations={"abif_raw": {"PBAS2": b"ACGT", "PCON2": [40, 41, 42, 43]}},
        seq="TTTT",
    )

    monkeypatch.setattr(abi_parser.SeqIO, "read", lambda *_args, **_kwargs: record)

    parsed = abi_parser.parse_ab1(b"fake")
    assert parsed["record_id"] == "rec-1"
    assert parsed["sequence"] == "ACGT"
    assert parsed["quality"] == [40, 41, 42, 43]
    assert parsed["warnings"] == []


def test_parse_ab1_fallbacks_when_fields_missing(monkeypatch: pytest.MonkeyPatch) -> None:
    record = FakeRecord(record_id="rec-2", annotations={"abif_raw": {}}, seq="GATTACA")
    monkeypatch.setattr(abi_parser.SeqIO, "read", lambda *_args, **_kwargs: record)

    parsed = abi_parser.parse_ab1(b"fake")
    assert parsed["sequence"] == "GATTACA"
    assert parsed["quality"] == []
    assert any("PBAS2" in warning for warning in parsed["warnings"])
    assert any("PCON2" in warning for warning in parsed["warnings"])


def test_parse_ab1_raises_clean_error_when_seqio_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    def raise_error(*_args, **_kwargs):
        raise RuntimeError("boom")

    monkeypatch.setattr(abi_parser.SeqIO, "read", raise_error)

    with pytest.raises(ValueError, match="Invalid or unsupported .ab1 file"):
        abi_parser.parse_ab1(b"invalid")
