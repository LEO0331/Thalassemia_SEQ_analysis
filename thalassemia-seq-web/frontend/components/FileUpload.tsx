import React from "react";

type FileUploadProps = {
  file: File | null;
  onFileChange: (file: File | null) => void;
};

export default function FileUpload({ file, onFileChange }: FileUploadProps) {
  return (
    <div className="panel control-panel">
      <p className="panel-eyebrow">Input</p>
      <label htmlFor="ab1-file" className="label">
        Upload `.ab1` file
      </label>
      <input
        id="ab1-file"
        type="file"
        accept=".ab1"
        onChange={(event) => onFileChange(event.target.files?.[0] ?? null)}
      />
      <p className="muted">{file ? `Selected: ${file.name}` : "No file selected"}</p>
    </div>
  );
}
