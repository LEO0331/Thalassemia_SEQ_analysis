from lib.quality_control import assess_quality


def test_quality_warns_on_mismatch_short_low_average_and_regions() -> None:
    sequence = "ACGTACGTAC"
    quality = [10, 10, 30, 30, 10, 10, 10]

    qc = assess_quality(sequence, quality, low_quality_threshold=20, min_sequence_length=20)

    assert qc["sequence_length"] == 10
    assert qc["average_quality"] == 15.71
    assert len(qc["low_quality_regions"]) == 2
    assert any("short" in warning.lower() for warning in qc["warnings"])
    assert any("mismatch" in warning.lower() for warning in qc["warnings"])
    assert any("below threshold" in warning.lower() for warning in qc["warnings"])
