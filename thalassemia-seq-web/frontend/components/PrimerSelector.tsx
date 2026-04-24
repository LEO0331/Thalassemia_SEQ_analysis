import React from "react";

type PrimerSelectorProps = {
  value: string;
  onChange: (value: string) => void;
};

const primers = ["T0128", "T0021", "T0133", "T0131", "T023", "T0145", "T024"];

export default function PrimerSelector({ value, onChange }: PrimerSelectorProps) {
  return (
    <div className="panel control-panel">
      <p className="panel-eyebrow">Target</p>
      <label htmlFor="primer" className="label">
        Primer / Target group
      </label>
      <select id="primer" value={value} onChange={(event) => onChange(event.target.value)}>
        {primers.map((primer) => (
          <option key={primer} value={primer}>
            {primer}
          </option>
        ))}
      </select>
      <p className="muted">Choose a group that matches the sequencing primer.</p>
    </div>
  );
}
