import React from "react";
import type { APIResult } from "../lib/types";

export default function ResultSummary({ result }: { result: APIResult }) {
  return (
    <div className="panel summary-panel">
      <p className="panel-eyebrow">Overview</p>
      <h3>Result Summary</h3>
      <div className="summary-metrics">
        <article>
          <span>File</span>
          <strong>{result.file_name}</strong>
        </article>
        <article>
          <span>Primer</span>
          <strong>{result.primer_type}</strong>
        </article>
        <article>
          <span>Sequence length</span>
          <strong>{result.qc.sequence_length}</strong>
        </article>
        <article>
          <span>Average quality</span>
          <strong>{result.qc.average_quality ?? "N/A"}</strong>
        </article>
      </div>
      <h4>Combined warnings</h4>
      {result.report.warnings.length > 0 ? (
        <ul>
          {result.report.warnings.map((warning) => (
            <li key={warning}>{warning}</li>
          ))}
        </ul>
      ) : (
        <p className="muted">No warnings</p>
      )}
      <p className="disclaimer">{result.report.disclaimer}</p>
    </div>
  );
}
