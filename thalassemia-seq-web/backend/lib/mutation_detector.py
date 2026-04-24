from __future__ import annotations

from lib.types import MutationHit, MutationSummary

SUPPORTED_PRIMERS = [
    "T0128",
    "T0021",
    "T0133",
    "T0131",
    "T023",
    "T0145",
    "T024",
]


def z_array(s: str) -> list[int]:
    assert len(s) > 1
    z = [len(s)] + [0] * (len(s) - 1)

    for i in range(1, len(s)):
        if s[i] == s[i - 1]:
            z[1] += 1
        else:
            break

    r, l = 0, 0
    if z[1] > 0:
        r, l = z[1], 1

    for k in range(2, len(s)):
        assert z[k] == 0
        if k > r:
            for i in range(k, len(s)):
                if s[i] == s[i - k]:
                    z[k] += 1
                else:
                    break
            r, l = k + z[k] - 1, k
        else:
            nbeta = r - k + 1
            zkp = z[k - l]
            if nbeta > zkp:
                z[k] = zkp
            else:
                nmatch = 0
                for i in range(r + 1, len(s)):
                    if s[i] == s[i - k]:
                        nmatch += 1
                    else:
                        break
                l, r = k, r + nmatch
                z[k] = r - k + 1
    return z


def n_array(s: str) -> list[int]:
    return z_array(s[::-1])[::-1]


def big_l_prime_array(p: str, n: list[int]) -> list[int]:
    lp = [0] * len(p)
    for j in range(len(p) - 1):
        i = len(p) - n[j]
        if i < len(p):
            lp[i] = j + 1
    return lp


def big_l_array(p: str, lp: list[int]) -> list[int]:
    l = [0] * len(p)
    l[1] = lp[1]
    for i in range(2, len(p)):
        l[i] = max(l[i - 1], lp[i])
    return l


def small_l_prime_array(n: list[int]) -> list[int]:
    small_lp = [0] * len(n)
    for i in range(len(n)):
        if n[i] == i + 1:
            small_lp[len(n) - i - 1] = i + 1
    for i in range(len(n) - 2, -1, -1):
        if small_lp[i] == 0:
            small_lp[i] = small_lp[i + 1]
    return small_lp


def good_suffix_table(p: str) -> tuple[list[int], list[int], list[int]]:
    n = n_array(p)
    lp = big_l_prime_array(p, n)
    return lp, big_l_array(p, lp), small_l_prime_array(n)


def dense_bad_char_tab(p: str, amap: dict[str, int]) -> list[list[int]]:
    tab: list[list[int]] = []
    nxt = [0] * len(amap)
    for i, c in enumerate(p):
        assert c in amap
        tab.append(nxt[:])
        nxt[amap[c]] = i + 1
    return tab


class BoyerMoore:
    def __init__(self, p: str, alphabet: str = "ACGT"):
        self.amap = {alphabet[i]: i for i in range(len(alphabet))}
        self.bad_char = dense_bad_char_tab(p, self.amap)
        _, self.big_l, self.small_l_prime = good_suffix_table(p)

    def bad_character_rule(self, i: int, c: str) -> int:
        assert c in self.amap
        ci = self.amap[c]
        return i - (self.bad_char[i][ci] - 1)

    def good_suffix_rule(self, i: int) -> int:
        length = len(self.big_l)
        if i == length - 1:
            return 0
        i += 1
        if self.big_l[i] > 0:
            return length - self.big_l[i]
        return length - self.small_l_prime[i]

    def match_skip(self) -> int:
        return len(self.small_l_prime) - self.small_l_prime[1]


def boyer_moore(pattern: str, pattern_bm: BoyerMoore, text: str) -> list[int]:
    i = 0
    occurrences: list[int] = []
    while i < len(text) - len(pattern) + 1:
        shift = 1
        mismatched = False
        for j in range(len(pattern) - 1, -1, -1):
            if pattern[j] != text[i + j]:
                skip_bc = pattern_bm.bad_character_rule(j, text[i + j])
                skip_gs = pattern_bm.good_suffix_rule(j)
                shift = max(shift, skip_bc, skip_gs)
                mismatched = True
                break
        if not mismatched:
            occurrences.append(i)
            shift = max(shift, pattern_bm.match_skip())
        i += shift
    return occurrences


def _legacy_qv(raw: int | str | None) -> int | None:
    if raw is None:
        return None
    if isinstance(raw, int):
        return raw - 33
    if isinstance(raw, str):
        if not raw:
            return None
        return ord(raw[0]) - 33
    return None


def _quality_at(quality: list[int], index: int) -> int | None:
    if index < 0 or index >= len(quality):
        return None
    return _legacy_qv(quality[index])


def _confidence(status: str, qv: int | None) -> str:
    if status == "uncertain":
        return "uncertain"
    if qv is None:
        return "low"
    if abs(qv) >= 10:
        return "high"
    if abs(qv) >= 3:
        return "medium"
    return "low"


def _single_site(
    results: list[MutationHit],
    sequence: str,
    quality: list[int],
    name: str,
    pattern: str,
    threshold: int,
    comparator: str,
) -> None:
    positions = boyer_moore(pattern, BoyerMoore(pattern), sequence)
    if not positions:
        results.append(
            {
                "name": name,
                "status": "mutation",
                "position": None,
                "matched_pattern": pattern,
                "quality_score": None,
                "confidence": "medium",
                "notes": "Reference pattern not found in sequence (legacy rule).",
            }
        )
        return

    pos = positions[0]
    qv = _quality_at(quality, pos)
    status = "WT"
    if qv is None:
        status = "uncertain"
    elif comparator == "lt" and qv < threshold:
        status = "heterozygous"
    elif comparator == "gt" and qv > threshold:
        status = "WT"
    elif comparator == "gt_else_other":
        status = "WT" if qv > threshold else "other mutant"

    results.append(
        {
            "name": name,
            "status": status,
            "position": pos,
            "matched_pattern": pattern,
            "quality_score": qv,
            "confidence": _confidence(status, qv),
            "notes": "Legacy single-site threshold rule.",
        }
    )


def _min_window_site(
    results: list[MutationHit],
    sequence: str,
    quality: list[int],
    name: str,
    pattern: str,
    offsets: list[int],
    threshold: int,
    pass_label: str = "WT",
    fail_label: str = "other mutant",
) -> tuple[int | None, int | None]:
    positions = boyer_moore(pattern, BoyerMoore(pattern), sequence)
    if not positions:
        results.append(
            {
                "name": name,
                "status": "mutation",
                "position": None,
                "matched_pattern": pattern,
                "quality_score": None,
                "confidence": "medium",
                "notes": "Reference pattern not found in sequence (legacy rule).",
            }
        )
        return None, None

    start = positions[0]
    qvs = [_quality_at(quality, start + off) for off in offsets]
    if any(qv is None for qv in qvs):
        status = "uncertain"
        min_qv = None
    else:
        min_qv = min(int(qv) for qv in qvs if qv is not None)
        status = pass_label if min_qv > threshold else fail_label

    results.append(
        {
            "name": name,
            "status": status,
            "position": start,
            "matched_pattern": pattern,
            "quality_score": min_qv,
            "confidence": _confidence(status, min_qv),
            "notes": f"Legacy multi-base threshold rule across offsets {offsets}.",
        }
    )
    return start, min_qv


def _run_t0128_family(sequence: str, quality: list[int], results: list[MutationHit]) -> None:
    _single_site(results, sequence, quality, "WS", "CGCCTCCC", threshold=0, comparator="lt")
    _single_site(results, sequence, quality, "QS", "TGGACAAG", threshold=0, comparator="lt")
    _single_site(results, sequence, quality, "CS", "TAAGCTGGAG", threshold=0, comparator="lt")


def _run_t0133_family(sequence: str, quality: list[int], results: list[MutationHit]) -> None:
    cd41_pos, _ = _min_window_site(
        results,
        sequence,
        quality,
        "CD41/42",
        "TTCTTTGAGTCCTTTG",
        offsets=[0, 1, 2, 3, 4, 5],
        threshold=-10,
    )
    if cd41_pos is not None:
        qv = _quality_at(quality, cd41_pos + 6)
        status = "uncertain" if qv is None else ("WT" if qv > -10 else "heterozygous")
        results.append(
            {
                "name": "CD43",
                "status": status,
                "position": cd41_pos + 6,
                "matched_pattern": "TTCTTTGAGTCCTTTG",
                "quality_score": qv,
                "confidence": _confidence(status, qv),
                "notes": "Legacy paired rule tied to CD41/42 anchor +6.",
            }
        )

    _min_window_site(
        results,
        sequence,
        quality,
        "CD71/72",
        "TAGTGAT",
        offsets=[0, 1],
        threshold=-10,
    )

    positions = boyer_moore("TGAGTCTATGGGA", BoyerMoore("TGAGTCTATGGGA"), sequence)
    if not positions:
        results.append(
            {
                "name": "IVS_II-2",
                "status": "mutation",
                "position": None,
                "matched_pattern": "TGAGTCTATGGGA",
                "quality_score": None,
                "confidence": "medium",
                "notes": "Reference pattern not found in sequence (legacy rule).",
            }
        )
        results.append(
            {
                "name": "IVS_II-5",
                "status": "uncertain",
                "position": None,
                "matched_pattern": "TGAGTCTATGGGA",
                "quality_score": None,
                "confidence": "uncertain",
                "notes": "TODO: legacy script only evaluates IVS_II-5 when IVS_II-2 anchor exists.",
            }
        )
        return

    anchor = positions[0]
    qv_ii2 = _quality_at(quality, anchor)
    status_ii2 = "uncertain" if qv_ii2 is None else ("WT" if qv_ii2 > -10 else "other mutant")
    results.append(
        {
            "name": "IVS_II-2",
            "status": status_ii2,
            "position": anchor,
            "matched_pattern": "TGAGTCTATGGGA",
            "quality_score": qv_ii2,
            "confidence": _confidence(status_ii2, qv_ii2),
            "notes": "Legacy single-position threshold (> -10).",
        }
    )

    qv_ii5 = _quality_at(quality, anchor + 3)
    status_ii5 = "uncertain" if qv_ii5 is None else ("heterozygous" if qv_ii5 < -10 else "WT")
    results.append(
        {
            "name": "IVS_II-5",
            "status": status_ii5,
            "position": anchor + 3,
            "matched_pattern": "TGAGTCTATGGGA",
            "quality_score": qv_ii5,
            "confidence": _confidence(status_ii5, qv_ii5),
            "notes": "Legacy offset +3 threshold (< -10).",
        }
    )


def _run_t023_family(sequence: str, quality: list[int], results: list[MutationHit], warnings: list[str]) -> None:
    positions = boyer_moore("CATAAAA", BoyerMoore("CATAAAA"), sequence)
    if not positions:
        results.append(
            {
                "name": "-32~-28",
                "status": "mutation",
                "position": None,
                "matched_pattern": "CATAAAA",
                "quality_score": None,
                "confidence": "medium",
                "notes": "Reference pattern not found in sequence (legacy rule).",
            }
        )
    else:
        anchor = positions[0]
        for offset, label in enumerate(["-32", "-31", "-30", "-29", "-28"]):
            qv = _quality_at(quality, anchor + offset)
            status = "uncertain" if qv is None else ("heterozygous" if qv < 0 else "WT")
            results.append(
                {
                    "name": label,
                    "status": status,
                    "position": anchor + offset,
                    "matched_pattern": "CATAAAA",
                    "quality_score": qv,
                    "confidence": _confidence(status, qv),
                    "notes": "Legacy per-position threshold (< 0).",
                }
            )

    _single_site(results, sequence, quality, "cap+1", "ACATTT", threshold=0, comparator="lt")
    _min_window_site(
        results,
        sequence,
        quality,
        "CAP+43~+40",
        "AAACAGACACC",
        offsets=[0, 1, 2, 3],
        threshold=0,
    )
    _single_site(results, sequence, quality, "InitCD", "TGGTGCA", threshold=0, comparator="lt")

    cd14_positions = boyer_moore("GTGGGGC", BoyerMoore("GTGGGGC"), sequence)
    cd14_anchor: int | None = cd14_positions[0] if cd14_positions else None
    if cd14_anchor is None:
        results.append(
            {
                "name": "CD14/15",
                "status": "mutation",
                "position": None,
                "matched_pattern": "GTGGGGC",
                "quality_score": None,
                "confidence": "medium",
                "notes": "Legacy shared-anchor rule: missing anchor indicates mutation.",
            }
        )
        results.append(
            {
                "name": "CD15/16",
                "status": "mutation",
                "position": None,
                "matched_pattern": "GTGGGGC",
                "quality_score": None,
                "confidence": "medium",
                "notes": "Legacy shared-anchor rule: missing anchor indicates mutation.",
            }
        )
    else:
        q14 = _quality_at(quality, cd14_anchor)
        q15 = _quality_at(quality, cd14_anchor + 1)
        q16 = _quality_at(quality, cd14_anchor + 4)

        cd1415_status = "uncertain"
        cd1516_status = "uncertain"
        score_1415: int | None = None
        score_1516: int | None = None

        if q14 is not None and q15 is not None:
            score_1415 = min(q14, q15)
            cd1415_status = "WT" if score_1415 > 0 else "other mutant"
        if q15 is not None and q16 is not None:
            score_1516 = min(q15, q16)
            cd1516_status = "WT" if score_1516 > 0 else "other mutant"

        results.append(
            {
                "name": "CD14/15",
                "status": cd1415_status,
                "position": cd14_anchor,
                "matched_pattern": "GTGGGGC",
                "quality_score": score_1415,
                "confidence": _confidence(cd1415_status, score_1415),
                "notes": "Legacy min([CD14, CD15]) > 0 rule.",
            }
        )
        results.append(
            {
                "name": "CD15/16",
                "status": cd1516_status,
                "position": cd14_anchor + 1,
                "matched_pattern": "GTGGGGC",
                "quality_score": score_1516,
                "confidence": _confidence(cd1516_status, score_1516),
                "notes": "Legacy min([CD15, CD16]) > 0 rule.",
            }
        )

    _single_site(results, sequence, quality, "CD17", "AAGGTGA", threshold=0, comparator="lt")
    _single_site(results, sequence, quality, "CD26", "GTGGGGC", threshold=0, comparator="lt")

    cd26_positions = boyer_moore("GTGGGGC", BoyerMoore("GTGGGGC"), sequence)
    if cd26_positions:
        anchor = cd26_positions[0]
        q27 = _quality_at(quality, anchor + 5)
        q28 = _quality_at(quality, anchor + 6)
        if q27 is None or q28 is None:
            status = "uncertain"
            score = None
        else:
            score = min(q27, q28)
            status = "WT" if score > 0 else "other mutant"
        results.append(
            {
                "name": "CD27/28",
                "status": status,
                "position": anchor + 5,
                "matched_pattern": "GTGGGGC",
                "quality_score": score,
                "confidence": _confidence(status, score),
                "notes": "Legacy min([CD27, CD28]) > 0 rule tied to CD26 anchor.",
            }
        )

    ivs_positions = boyer_moore("AGGTTGGT", BoyerMoore("AGGTTGGT"), sequence)
    if not ivs_positions:
        results.append(
            {
                "name": "IVS-I_-2",
                "status": "mutation",
                "position": None,
                "matched_pattern": "AGGTTGGT",
                "quality_score": None,
                "confidence": "medium",
                "notes": "Reference pattern not found in sequence (legacy rule).",
            }
        )
    else:
        ivs_anchor = ivs_positions[0]
        q_ivs2 = _quality_at(quality, ivs_anchor)
        status_ivs2 = "uncertain" if q_ivs2 is None else ("heterozygous" if q_ivs2 < 0 else "WT")
        results.append(
            {
                "name": "IVS-I_-2",
                "status": status_ivs2,
                "position": ivs_anchor,
                "matched_pattern": "AGGTTGGT",
                "quality_score": q_ivs2,
                "confidence": _confidence(status_ivs2, q_ivs2),
                "notes": "Legacy per-position threshold (< 0).",
            }
        )

        # TODO: Legacy notebook uses `b` (CD14 anchor) for IVS-I-1 and IVS-I-5 offsets.
        # This appears to be a copy/paste coupling; we preserve that behavior with warning.
        base_anchor = cd14_anchor if cd14_anchor is not None else ivs_anchor
        if cd14_anchor is None:
            warnings.append(
                "TODO: IVS-I-1/IVS-I-5 legacy offsets are normally tied to CD14 anchor; fallback used IVS-I anchor."
            )

        for offset, name in [(2, "IVS-I-1"), (6, "IVS-I-5")]:
            qv = _quality_at(quality, base_anchor + offset)
            status = "uncertain" if qv is None else ("heterozygous" if qv < 0 else "WT")
            results.append(
                {
                    "name": name,
                    "status": status,
                    "position": base_anchor + offset,
                    "matched_pattern": "AGGTTGGT",
                    "quality_score": qv,
                    "confidence": _confidence(status, qv),
                    "notes": "Legacy offset rule inherited from notebook implementation.",
                }
            )

    _single_site(results, sequence, quality, "CD31", "CTGCTGGT", threshold=0, comparator="gt_else_other")
    _single_site(results, sequence, quality, "CD37", "GACCCA", threshold=0, comparator="lt")
    _single_site(results, sequence, quality, "CD38", "ACCCA", threshold=0, comparator="lt")


def _run_t024(sequence: str, quality: list[int], results: list[MutationHit]) -> None:
    _single_site(results, sequence, quality, "IVS-II-654", "GCCTTAACCCAG", threshold=0, comparator="lt")


def _normalize_primer(primer_type: str, warnings: list[str]) -> str:
    primer = primer_type.strip().upper()
    aliases = {
        "T0021": "T0128",
        "T0131": "T0133",
        "T0145": "T023",
        "T0023": "T023",
        "T0024": "T024",
    }
    if primer in aliases:
        canonical = aliases[primer]
        warnings.append(
            f"Primer {primer} is mapped to {canonical} based on paired legacy notebook structure."
        )
        return canonical
    return primer


def detect_mutations(sequence: str, quality: list[int], primer_type: str) -> MutationSummary:
    warnings: list[str] = []
    canonical = _normalize_primer(primer_type, warnings)

    if canonical not in {"T0128", "T0133", "T023", "T024"}:
        raise ValueError(f"Unsupported primer type: {primer_type}")

    results: list[MutationHit] = []
    if canonical == "T0128":
        _run_t0128_family(sequence, quality, results)
    elif canonical == "T0133":
        _run_t0133_family(sequence, quality, results)
    elif canonical == "T023":
        _run_t023_family(sequence, quality, results, warnings)
    elif canonical == "T024":
        _run_t024(sequence, quality, results)

    return {
        "primer_type": primer_type,
        "sequence_length": len(sequence),
        "mutations": results,
        "warnings": warnings,
    }
