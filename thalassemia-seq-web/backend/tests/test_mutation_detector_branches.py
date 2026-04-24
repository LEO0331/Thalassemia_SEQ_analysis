from __future__ import annotations

import pytest

import lib.mutation_detector as md


def _build_sequence_for_t023() -> str:
    return (
        "TTTCATAAAATTTACATTTGGGAAACAGACACCTTTTGGTGCATTTGTGGGGCTTTAAGGTGATTT"
        "AGGTTGGTTTTCTGCTGGTTTTGACCCATTTACCCATTT"
    )


def test_algorithm_helpers_cover_bm_tables() -> None:
    z = md.z_array("AAAAA")
    assert z[0] == 5
    assert md.n_array("ACGT") == [0, 0, 0, 4]

    n = md.n_array("AACAAC")
    lp = md.big_l_prime_array("AACAAC", n)
    l = md.big_l_array("AACAAC", lp)
    slp = md.small_l_prime_array(n)
    assert len(lp) == len(l) == len(slp) == 6

    bm = md.BoyerMoore("ACGT")
    assert bm.good_suffix_rule(3) == 0
    assert bm.bad_character_rule(1, "C") >= 0
    with pytest.raises(AssertionError):
        bm.bad_character_rule(1, "N")


def test_low_level_confidence_and_quality_helpers() -> None:
    assert md._legacy_qv(None) is None
    assert md._legacy_qv(40) == 7
    assert md._legacy_qv("A") == 32
    assert md._legacy_qv("") is None

    assert md._quality_at([40], 10) is None
    assert md._quality_at([40], 0) == 7

    assert md._confidence("uncertain", None) == "uncertain"
    assert md._confidence("WT", None) == "low"
    assert md._confidence("WT", 12) == "high"
    assert md._confidence("WT", 4) == "medium"
    assert md._confidence("WT", 1) == "low"


def test_single_site_and_min_window_branching() -> None:
    results: list[dict] = []
    md._single_site(results, "AAAA", [40, 40, 40, 40], "X", "TT", 0, "lt")
    assert results[-1]["status"] == "mutation"

    results = []
    md._single_site(results, "ACGT", [], "X", "AC", 0, "lt")
    assert results[-1]["status"] == "uncertain"

    results = []
    md._single_site(results, "ACGT", [20, 40, 40, 40], "X", "AC", 0, "lt")
    assert results[-1]["status"] == "heterozygous"

    results = []
    md._single_site(results, "ACGT", [40, 40, 40, 40], "X", "AC", 0, "gt_else_other")
    assert results[-1]["status"] == "WT"

    results = []
    md._single_site(results, "ACGT", [30, 40, 40, 40], "X", "AC", 0, "gt_else_other")
    assert results[-1]["status"] == "other mutant"

    results = []
    md._min_window_site(results, "ACGT", [], "X", "AC", [0, 1], 0)
    assert results[-1]["status"] == "uncertain"


def test_detect_mutations_t0133_with_missing_ivs_pattern() -> None:
    sequence = "TTCTTTGAGTCCTTTGTTTTAGTGATTTTT"
    quality = [40] * len(sequence)

    result = md.detect_mutations(sequence, quality, "T0133")
    names = {item["name"]: item for item in result["mutations"]}

    assert names["CD41/42"]["status"] == "WT"
    assert names["CD43"]["status"] == "WT"
    assert names["IVS_II-2"]["status"] == "mutation"
    assert names["IVS_II-5"]["status"] == "uncertain"


def test_detect_mutations_t0133_with_present_ivs_pattern_and_low_quality() -> None:
    sequence = "TTCTTTGAGTCCTTTGTTTTAGTGATTTTTTGAGTCTATGGGATTT"
    quality = [40] * len(sequence)
    anchor = sequence.index("TGAGTCTATGGGA")
    quality[anchor] = 10
    quality[anchor + 3] = 10

    result = md.detect_mutations(sequence, quality, "T0131")
    names = {item["name"]: item for item in result["mutations"]}

    assert any("mapped to T0133" in warning for warning in result["warnings"])
    assert names["IVS_II-2"]["status"] == "other mutant"
    assert names["IVS_II-5"]["status"] == "heterozygous"


def test_detect_mutations_t023_branches_and_alias_warning() -> None:
    sequence = _build_sequence_for_t023()
    quality = [40] * len(sequence)

    # Force uncertain branch for CD27/28 via out-of-range quality lookup
    quality = quality[: sequence.index("GTGGGGC") + 6]

    result = md.detect_mutations(sequence, quality, "T0145")
    names = {item["name"]: item for item in result["mutations"]}

    assert any("mapped to T023" in warning for warning in result["warnings"])
    assert names["-32"]["status"] in {"WT", "uncertain", "heterozygous"}
    assert names["CD14/15"]["status"] in {"WT", "other mutant", "uncertain"}
    assert names["CD27/28"]["status"] == "uncertain"
    assert names["IVS-I_-2"]["name"] == "IVS-I_-2"


def test_detect_mutations_t023_missing_anchor_paths() -> None:
    sequence = "ACATTTAAACAGACACCTGGTGCA"
    quality = [40] * len(sequence)

    result = md.detect_mutations(sequence, quality, "T023")
    names = {item["name"]: item for item in result["mutations"]}

    assert names["-32~-28"]["status"] == "mutation"
    assert names["CD14/15"]["status"] == "mutation"
    assert names["IVS-I_-2"]["status"] == "mutation"


def test_detect_mutations_t024_alias_and_direct() -> None:
    seq = "TTTGCCTTAACCCAGTTT"
    quality = [20] * len(seq)

    direct = md.detect_mutations(seq, quality, "T024")
    alias = md.detect_mutations(seq, quality, "T0024")

    assert direct["mutations"][0]["status"] == "heterozygous"
    assert any("mapped to T024" in warning for warning in alias["warnings"])


def test_detect_mutations_rejects_unknown() -> None:
    with pytest.raises(ValueError, match="Unsupported primer type"):
        md.detect_mutations("ACGT", [40, 40, 40, 40], "BAD")
