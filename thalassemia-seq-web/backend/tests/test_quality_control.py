from lib.quality_control import assess_quality


def test_quality_reports_sequence_length_and_average() -> None:
    sequence = "ACGTACGT"
    quality = [30, 31, 32, 33, 30, 30, 31, 32]
    qc = assess_quality(sequence, quality, low_quality_threshold=20, min_sequence_length=4)

    assert qc["sequence_length"] == 8
    assert qc["average_quality"] == 31.12
    assert qc["warnings"] == []


def test_quality_handles_missing_quality() -> None:
    sequence = "ACGT"
    qc = assess_quality(sequence, [], min_sequence_length=2)

    assert qc["sequence_length"] == 4
    assert qc["average_quality"] is None
    assert any("missing" in warning.lower() for warning in qc["warnings"])
