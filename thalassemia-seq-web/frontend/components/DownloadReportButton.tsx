import React from "react";

type DownloadReportButtonProps = {
  report: unknown;
  fileName?: string;
};

export default function DownloadReportButton({
  report,
  fileName = "mutation-report.json",
}: DownloadReportButtonProps) {
  const download = () => {
    const blob = new Blob([JSON.stringify(report, null, 2)], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = fileName;
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
  };

  return (
    <button className="btn btn-primary" type="button" onClick={download}>
      Download JSON report
    </button>
  );
}
