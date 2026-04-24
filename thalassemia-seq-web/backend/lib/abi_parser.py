from __future__ import annotations

from io import BytesIO

from Bio import SeqIO

from lib.types import ParsedABI


def _normalize_sequence(value: object) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("ascii", errors="ignore")
    if isinstance(value, str):
        return value
    if isinstance(value, (list, tuple)):
        return "".join(str(part) for part in value)
    return str(value)


def _normalize_quality(value: object) -> list[int]:
    if value is None:
        return []
    if isinstance(value, bytes):
        return [int(byte) for byte in value]
    if isinstance(value, str):
        return [ord(char) for char in value]
    if isinstance(value, (list, tuple)):
        normalized: list[int] = []
        for entry in value:
            if isinstance(entry, int):
                normalized.append(entry)
            elif isinstance(entry, str) and entry:
                normalized.append(ord(entry[0]))
            else:
                try:
                    normalized.append(int(entry))
                except (TypeError, ValueError):
                    continue
        return normalized
    return []


def parse_ab1(file_bytes: bytes) -> ParsedABI:
    """Parse an uploaded ABI/Sanger `.ab1` file into JSON-serializable fields."""
    warnings: list[str] = []

    try:
        record = SeqIO.read(BytesIO(file_bytes), "abi")
    except Exception as exc:  # pragma: no cover - exact exception types differ by BioPython version
        raise ValueError("Invalid or unsupported .ab1 file.") from exc

    raw = record.annotations.get("abif_raw", {})

    sequence = _normalize_sequence(raw.get("PBAS2"))
    if not sequence:
        sequence = _normalize_sequence(record.seq)
        warnings.append("PBAS2 field missing; used record.seq fallback.")

    quality = _normalize_quality(raw.get("PCON2"))
    if not quality:
        warnings.append("PCON2 quality scores missing.")

    parsed: ParsedABI = {
        "record_id": str(record.id),
        "sequence": sequence,
        "quality": quality,
        "length": len(sequence),
        "warnings": warnings,
    }
    return parsed
