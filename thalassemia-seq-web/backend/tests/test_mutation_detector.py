import pytest

from lib.mutation_detector import detect_mutations


def test_mutation_detector_rejects_unsupported_primer() -> None:
    with pytest.raises(ValueError):
        detect_mutations("ACGTACGT", [40] * 8, "T9999")


def test_mutation_detector_detects_known_t0128_pattern() -> None:
    sequence = "AAAACGCCTCCCTTTTGGACAAGGGGTAAGCTGGAGAAAA"
    quality = [40] * len(sequence)
    result = detect_mutations(sequence, quality, "T0128")

    ws = next(item for item in result["mutations"] if item["name"] == "WS")
    assert ws["status"] == "WT"
    assert ws["position"] is not None


def test_mutation_detector_handles_missing_pattern_as_mutation() -> None:
    sequence = "AAAAAAAATTTTTTTTCCCCCCCCGGGGGGGG"
    quality = [40] * len(sequence)
    result = detect_mutations(sequence, quality, "T024")

    ivs = result["mutations"][0]
    assert ivs["name"] == "IVS-II-654"
    assert ivs["status"] == "mutation"
