from __future__ import annotations

from lib.types import LowQualityRegion, QCSummary


def assess_quality(
    sequence: str,
    quality: list[int],
    low_quality_threshold: int = 20,
    min_sequence_length: int = 50,
) -> QCSummary:
    warnings: list[str] = []
    sequence_length = len(sequence)

    if sequence_length < min_sequence_length:
        warnings.append(
            f"Sequence length is short ({sequence_length} bases). Minimum recommended is {min_sequence_length}."
        )

    if not quality:
        warnings.append("Quality scores are missing; confidence estimates are limited.")
        return {
            "sequence_length": sequence_length,
            "average_quality": None,
            "low_quality_regions": [],
            "warnings": warnings,
        }

    if len(quality) != sequence_length:
        warnings.append(
            f"Sequence/quality length mismatch: sequence={sequence_length}, quality={len(quality)}."
        )

    avg_quality = sum(quality) / len(quality)

    if avg_quality < low_quality_threshold:
        warnings.append(
            f"Average quality ({avg_quality:.2f}) is below threshold ({low_quality_threshold})."
        )

    low_quality_regions: list[LowQualityRegion] = []
    start_idx: int | None = None
    for idx, score in enumerate(quality):
        if score < low_quality_threshold:
            if start_idx is None:
                start_idx = idx
        elif start_idx is not None:
            segment = quality[start_idx:idx]
            low_quality_regions.append(
                {
                    "start": start_idx,
                    "end": idx - 1,
                    "average_quality": round(sum(segment) / len(segment), 2),
                }
            )
            start_idx = None

    if start_idx is not None:
        segment = quality[start_idx:]
        low_quality_regions.append(
            {
                "start": start_idx,
                "end": len(quality) - 1,
                "average_quality": round(sum(segment) / len(segment), 2),
            }
        )

    return {
        "sequence_length": sequence_length,
        "average_quality": round(avg_quality, 2),
        "low_quality_regions": low_quality_regions,
        "warnings": warnings,
    }
