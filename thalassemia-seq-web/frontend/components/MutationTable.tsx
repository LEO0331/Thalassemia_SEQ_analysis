import React from "react";
import type { Mutation } from "../lib/types";

function statusClass(status: string): string {
  const normalized = status.toLowerCase();
  if (normalized === "wt") return "pill pill-good";
  if (normalized.includes("uncertain")) return "pill pill-uncertain";
  if (normalized.includes("heterozygous")) return "pill pill-mid";
  return "pill pill-alert";
}

export default function MutationTable({ mutations }: { mutations: Mutation[] }) {
  return (
    <div className="panel mutation-panel">
      <p className="panel-eyebrow">Analysis</p>
      <h3>Mutation Results</h3>
      <div className="table-wrap">
        <table>
          <thead>
            <tr>
              <th>Mutation</th>
              <th>Status</th>
              <th>Position</th>
              <th>Matched pattern</th>
              <th>Quality</th>
              <th>Confidence</th>
              <th>Notes</th>
            </tr>
          </thead>
          <tbody>
            {mutations.map((mutation, index) => (
              <tr key={`${mutation.name}-${index}`}>
                <td>{mutation.name}</td>
                <td>
                  <span className={statusClass(mutation.status)}>{mutation.status}</span>
                </td>
                <td>{mutation.position ?? "N/A"}</td>
                <td className="mono">{mutation.matched_pattern}</td>
                <td>{mutation.quality_score ?? "N/A"}</td>
                <td>{mutation.confidence}</td>
                <td>{mutation.notes}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
}
