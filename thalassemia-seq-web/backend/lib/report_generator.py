from __future__ import annotations

from collections import Counter


def generate_report(
    file_name: str,
    primer_type: str,
    parsed: dict,
    qc: dict,
    analysis: dict,
) -> dict:
    combined_warnings: list[str] = []
    for section in (parsed, qc, analysis):
        for warning in section.get("warnings", []):
            if warning not in combined_warnings:
                combined_warnings.append(warning)

    status_counts = Counter(item.get("status", "unknown") for item in analysis.get("mutations", []))

    return {
        "file_name": file_name,
        "primer_type": primer_type,
        "sequence_length": parsed.get("length", 0),
        "qc_summary": qc,
        "mutation_summary": {
            "total_mutations": len(analysis.get("mutations", [])),
            "status_counts": dict(status_counts),
            "mutations": analysis.get("mutations", []),
        },
        "warnings": combined_warnings,
        "disclaimer": (
            "This tool is for educational/research workflow support only and "
            "must not be used as a standalone clinical diagnostic tool."
        ),
    }
