"use client";

import React, { useMemo, useState } from "react";

import DownloadReportButton from "../components/DownloadReportButton";
import FileUpload from "../components/FileUpload";
import MutationTable from "../components/MutationTable";
import PrimerSelector from "../components/PrimerSelector";
import QCPanel from "../components/QCPanel";
import ResultSummary from "../components/ResultSummary";
import type { APIError, APIResult } from "../lib/types";

export default function HomePage() {
  const [file, setFile] = useState<File | null>(null);
  const [primer, setPrimer] = useState("T0128");
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [result, setResult] = useState<APIResult | null>(null);

  const apiBase = useMemo(() => (process.env.NEXT_PUBLIC_API_BASE_URL ?? "").replace(/\/$/, ""), []);

  const runAnalysis = async () => {
    setError(null);
    setResult(null);

    if (!file) {
      setError("Please upload an .ab1 file.");
      return;
    }

    setLoading(true);
    try {
      const formData = new FormData();
      formData.append("file", file);
      formData.append("primer_type", primer);

      const response = await fetch(`${apiBase}/api/analyze`, {
        method: "POST",
        body: formData,
      });

      const payload = (await response.json()) as APIResult | APIError;
      if (!response.ok || !payload.ok) {
        const message = "error" in payload ? payload.error.message : "Analysis failed.";
        throw new Error(message);
      }

      setResult(payload);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Unexpected error.");
    } finally {
      setLoading(false);
    }
  };

  const loadDemo = async () => {
    setError(null);
    setLoading(true);
    try {
      const response = await fetch("/examples/demo-result.json");
      if (!response.ok) {
        throw new Error("Unable to load demo result.");
      }
      const payload = (await response.json()) as APIResult;
      setResult(payload);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Unexpected error.");
    } finally {
      setLoading(false);
    }
  };

  return (
    <main className="page-shell">
      <section className="hero panel">
        <p className="hero-kicker">Research Workflow Interface</p>
        <h1 className="hero-title">Thalassemia Sanger Sequencing Mutation Checker</h1>
        <p className="hero-copy">
          Upload Sanger sequencing `.ab1` files and check primer-specific thalassemia mutation patterns.
        </p>
        <div className="hero-ribbon" aria-hidden="true">
          <span>ABI Parsing</span>
          <span>Primer Rules</span>
          <span>QC Summary</span>
          <span>JSON Report</span>
        </div>
      </section>

      <section className="control-grid">
        <FileUpload file={file} onFileChange={setFile} />
        <PrimerSelector value={primer} onChange={setPrimer} />
      </section>

      <section className="panel actions-panel">
        <div className="actions">
          <button className="btn btn-primary" type="button" onClick={runAnalysis} disabled={loading}>
            {loading ? "Analyzing..." : "Analyze"}
          </button>
          <button className="btn btn-secondary" type="button" onClick={loadDemo} disabled={loading}>
            Load demo result
          </button>
        </div>
        <p className="muted small">
          Supported groups: T0128, T0021, T0133, T0131, T023, T0145, T024
        </p>
      </section>

      {error && (
        <p className="error" role="alert">
          {error}
        </p>
      )}

      {result && (
        <section className="result-stack" aria-live="polite">
          <ResultSummary result={result} />
          <QCPanel qc={result.qc} />
          <MutationTable mutations={result.analysis.mutations} />
          <section className="panel">
            <DownloadReportButton report={result.report} fileName={`${result.file_name}.report.json`} />
          </section>
        </section>
      )}
    </main>
  );
}
