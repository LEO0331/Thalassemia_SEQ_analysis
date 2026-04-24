import React from "react";
import type { APIResult } from "../lib/types";

type QCData = {
  sequence_length: APIResult["qc"]["sequence_length"];
  average_quality: APIResult["qc"]["average_quality"];
  low_quality_regions: APIResult["qc"]["low_quality_regions"];
  warnings: APIResult["qc"]["warnings"];
};

export default function QCPanel({ qc }: { qc: QCData }) {
  return (
    <div className="panel qc-panel">
      <p className="panel-eyebrow">Quality</p>
      <h3>Quality Control</h3>
      <div className="qc-grid">
        <p>
          <span>Sequence length</span>
          <strong>{qc.sequence_length}</strong>
        </p>
        <p>
          <span>Average quality</span>
          <strong>{qc.average_quality ?? "N/A"}</strong>
        </p>
        <p>
          <span>Low-quality regions</span>
          <strong>{qc.low_quality_regions.length}</strong>
        </p>
      </div>
      {qc.warnings.length > 0 && (
        <ul>
          {qc.warnings.map((warning) => (
            <li key={warning}>{warning}</li>
          ))}
        </ul>
      )}
    </div>
  );
}
