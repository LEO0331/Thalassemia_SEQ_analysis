# Thalassemia Sanger Sequencing Mutation Checker

## Project layers (current view)
```text
thalassemia-seq-web/
  frontend/   # Next.js UI (upload, primer selection, result rendering)
  backend/    # FastAPI + ABI/QC/mutation/report logic + tests
  vercel.json # optional combined routing definition
```

## 1. Project title
Thalassemia Sanger Sequencing Mutation Checker

## 2. Project overview
A full-stack prototype that refactors this repository's original notebook/script workflow into a web app for `.ab1` upload, primer-specific mutation checking, QC visualization, and JSON report export.

## 3. What the tool does
- Upload ABI/Sanger `.ab1` files
- Select a primer/target group
- Parse sequence + quality data
- Run primer-specific mutation checks based on legacy notebook logic
- Show QC + mutation results in the browser
- Download structured JSON reports

## 4. Original repo background
The original repository contained Jupyter notebooks and exported Python scripts with hardcoded local paths and script-style execution for thalassemia mutation checking. This refactor preserves the legacy biological assumptions where identifiable and surfaces ambiguity as warnings/TODO notes.

## 5. Features
- Next.js frontend
- Python FastAPI backend (`POST /api/analyze`)
- ABI parsing with BioPython
- QC summary with warnings
- Primer-based mutation detection
- Demo mode from static JSON
- JSON report download
- Pytest coverage for core backend modules

## 6. Supported primer/target groups
Supported inputs:
- `T0128`
- `T0021`
- `T0133`
- `T0131`
- `T023`
- `T0145`
- `T024`

Compatibility aliases from source data:
- `T0023` -> `T023`
- `T0024` -> `T024`

Notes:
- Legacy notebooks are paired (`T0128/T0021`, `T0133/T0131`, `T023/T0145`), so paired groups currently share the same rule set with warnings in output.

## 7. Local setup
From `thalassemia-seq-web`:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r backend/requirements.txt
cd frontend && npm install
```

## 8. Frontend run command
```bash
cd frontend
npm run dev
```

## 9. Backend/API run command
```bash
cd backend
uvicorn api.analyze:app --reload --port 8000
```

Frontend can call the backend by setting:

```bash
NEXT_PUBLIC_API_BASE_URL=http://localhost:8000
```

If `NEXT_PUBLIC_API_BASE_URL` is unset, frontend calls `/api/analyze` on same origin.

## 10. Test command
```bash
cd backend
pytest
```

## 11. Vercel deployment guide
Option A (single deployment, if Python API works on your Vercel setup):
1. Deploy `thalassemia-seq-web` to Vercel.
2. Ensure `vercel.json`, `frontend/`, and `backend/api/analyze.py` are included.
3. Frontend can call same-origin `/api/analyze`.

## 12. Fallback deployment guide
Option B (recommended if Python serverless limits block your workload):
1. Deploy Next.js frontend on Vercel.
2. Deploy Python API (`backend/api/analyze.py` equivalent FastAPI service) on Render/Fly.io/Railway.
3. Set Vercel env var:

```bash
NEXT_PUBLIC_API_BASE_URL=https://your-python-api.example.com
```

## 13. Example workflow
1. Open the web UI.
2. Select a primer group.
3. Upload an `.ab1` file.
4. Click Analyze.
5. Inspect QC and mutation table.
6. Download JSON report.
7. Optionally click "Load demo result" without backend calls.

## 14. Limitations
- Rules are preserved from research notebooks and may include legacy ambiguities.
- Some primer groups are mapped from paired notebooks rather than independent rule files.
- This MVP does not perform chromatogram visualization.
- Legacy quality interpretation uses source sign/threshold behavior and should be interpreted cautiously.

## 15. Clinical disclaimer
Disclaimer:
This tool is for educational and research workflow support only. It must not be used as a standalone clinical diagnostic tool. Any clinical interpretation should be reviewed and validated by qualified professionals using approved laboratory procedures.
