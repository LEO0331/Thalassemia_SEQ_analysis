# Thalassemia Sanger Sequencing Mutation Checker

A practical web tool for primer-specific review of Sanger sequencing `.ab1` files used in thalassemia mutation screening workflows.

## What This Project Is
This repository provides a full-stack prototype that helps users:
- Upload `.ab1` Sanger sequencing files
- Select target primer groups
- Run deterministic mutation and QC checks
- Review results in a browser
- Export a structured JSON report

## Who It Is For
- Research labs and academic workflows
- Bioinformatics support teams
- Internal validation and training use cases

## Important Disclaimer
This tool is for educational and research workflow support only.
It must not be used as a standalone clinical diagnostic tool.
Any clinical interpretation should be reviewed and validated by qualified professionals using approved laboratory procedures.

## Project Layout
- `thalassemia-seq-web/` - deployable full-stack application
  - `frontend/` - Next.js web interface
  - `backend/` - Python FastAPI + ABI/QC/mutation logic
- `notebooks/` - original exploratory Jupyter notebooks
- `Dataset and py/` - legacy scripts and sample/archived assets

## Quick Start
See the implementation guide in:
- `thalassemia-seq-web/README.md`
