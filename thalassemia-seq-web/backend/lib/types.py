from __future__ import annotations

from typing import Any, Literal, TypedDict


MutationStatus = Literal["detected", "WT", "heterozygous", "other mutant", "mutation", "uncertain"]
ConfidenceLevel = Literal["high", "medium", "low", "uncertain"]


class LowQualityRegion(TypedDict):
    start: int
    end: int
    average_quality: float


class QCSummary(TypedDict):
    sequence_length: int
    average_quality: float | None
    low_quality_regions: list[LowQualityRegion]
    warnings: list[str]


class MutationHit(TypedDict):
    name: str
    status: MutationStatus
    position: int | None
    matched_pattern: str
    quality_score: int | None
    confidence: ConfidenceLevel
    notes: str


class MutationSummary(TypedDict):
    primer_type: str
    sequence_length: int
    mutations: list[MutationHit]
    warnings: list[str]


class ParsedABI(TypedDict):
    record_id: str
    sequence: str
    quality: list[int]
    length: int
    warnings: list[str]


class APIError(TypedDict):
    code: str
    message: str


class APIResponse(TypedDict, total=False):
    ok: bool
    file_name: str
    primer_type: str
    qc: QCSummary
    analysis: MutationSummary
    report: dict[str, Any]
    error: APIError
