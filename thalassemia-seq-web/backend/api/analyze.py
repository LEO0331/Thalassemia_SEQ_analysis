from __future__ import annotations

from fastapi import FastAPI, File, Form, Request, UploadFile
from fastapi.responses import JSONResponse

from lib.abi_parser import parse_ab1
from lib.mutation_detector import SUPPORTED_PRIMERS, detect_mutations
from lib.quality_control import assess_quality
from lib.report_generator import generate_report

MAX_FILE_SIZE_BYTES = 5 * 1024 * 1024
ABIF_MAGIC = b"ABIF"

app = FastAPI(title="Thalassemia Sanger Sequencing Mutation Checker API")


def _error(code: str, message: str, status_code: int) -> JSONResponse:
    return JSONResponse(
        status_code=status_code,
        content={
            "ok": False,
            "error": {
                "code": code,
                "message": message,
            },
        },
    )


@app.post("/api/analyze")
async def analyze(
    request: Request,
    file: UploadFile | None = File(None),
    primer_type: str = Form(...),
) -> JSONResponse:
    if not file:
        return _error("MISSING_FILE", "No file uploaded.", 400)

    file_name = file.filename or "uploaded.ab1"
    if not file_name.lower().endswith(".ab1"):
        return _error("INVALID_FILE_TYPE", "Only .ab1 files are supported.", 400)

    normalized_primer = primer_type.strip().upper()
    if normalized_primer not in set(SUPPORTED_PRIMERS + ["T0023", "T0024"]):
        return _error(
            "INVALID_PRIMER_TYPE",
            f"Unsupported primer_type. Supported values: {', '.join(SUPPORTED_PRIMERS)}",
            400,
        )

    content_length = request.headers.get("content-length")
    if content_length and content_length.isdigit() and int(content_length) > (MAX_FILE_SIZE_BYTES + 4096):
        return _error(
            "FILE_TOO_LARGE",
            f"File is too large. Max size is {MAX_FILE_SIZE_BYTES // (1024 * 1024)} MB.",
            413,
        )

    data = bytearray()
    chunk_size = 1024 * 1024
    while True:
        chunk = await file.read(chunk_size)
        if not chunk:
            break
        data.extend(chunk)
        if len(data) > MAX_FILE_SIZE_BYTES:
            return _error(
                "FILE_TOO_LARGE",
                f"File is too large. Max size is {MAX_FILE_SIZE_BYTES // (1024 * 1024)} MB.",
                413,
            )

    if not data:
        return _error("INVALID_FILE_TYPE", "Uploaded file is empty.", 400)
    if len(data) > MAX_FILE_SIZE_BYTES:
        return _error(
            "FILE_TOO_LARGE",
            f"File is too large. Max size is {MAX_FILE_SIZE_BYTES // (1024 * 1024)} MB.",
            413,
        )
    if len(data) < len(ABIF_MAGIC) or data[:4] != ABIF_MAGIC:
        return _error(
            "INVALID_FILE_TYPE",
            "Only valid ABI/.ab1 binary files are supported.",
            400,
        )

    try:
        parsed = parse_ab1(bytes(data))
    except ValueError:
        return _error("ABI_PARSE_ERROR", "Invalid or unsupported .ab1 file.", 400)

    try:
        qc = assess_quality(parsed["sequence"], parsed["quality"])
        analysis = detect_mutations(parsed["sequence"], parsed["quality"], normalized_primer)
        report = generate_report(file_name, normalized_primer, parsed, qc, analysis)
    except ValueError as exc:
        return _error("INVALID_PRIMER_TYPE", str(exc), 400)
    except Exception:
        return _error("ANALYSIS_ERROR", "Analysis failed for this file.", 500)

    return JSONResponse(
        content={
            "ok": True,
            "file_name": file_name,
            "primer_type": normalized_primer,
            "qc": qc,
            "analysis": analysis,
            "report": report,
        }
    )


@app.get("/api/health")
async def health() -> dict[str, str]:
    return {"status": "ok"}
