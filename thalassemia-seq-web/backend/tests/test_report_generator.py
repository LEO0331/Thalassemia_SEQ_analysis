from lib.report_generator import generate_report


def test_generate_report_merges_warnings_and_counts_statuses() -> None:
    parsed = {"length": 12, "warnings": ["w1", "w2"]}
    qc = {"warnings": ["w2", "w3"]}
    analysis = {
        "warnings": ["w3", "w4"],
        "mutations": [
            {"status": "WT"},
            {"status": "heterozygous"},
            {"status": "WT"},
            {},
        ],
    }

    report = generate_report("sample.ab1", "T0128", parsed, qc, analysis)

    assert report["file_name"] == "sample.ab1"
    assert report["sequence_length"] == 12
    assert report["mutation_summary"]["total_mutations"] == 4
    assert report["mutation_summary"]["status_counts"] == {"WT": 2, "heterozygous": 1, "unknown": 1}
    assert report["warnings"] == ["w1", "w2", "w3", "w4"]
    assert "must not be used as a standalone clinical diagnostic tool" in report["disclaimer"]
