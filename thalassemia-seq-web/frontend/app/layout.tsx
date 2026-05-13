import "./globals.css";
import type { Metadata } from "next";
import React from "react";

export const metadata: Metadata = {
  title: "Thalassemia Sanger Sequencing Mutation Checker",
  description:
    "Upload Sanger sequencing .ab1 files and check primer-specific thalassemia mutation patterns.",
  metadataBase: new URL("https://thalassemia-seq-web.vercel.app"),
  robots: {
    index: true,
    follow: true,
  },
  openGraph: {
    title: "Thalassemia Sanger Sequencing Mutation Checker",
    description:
      "Upload Sanger sequencing .ab1 files and check primer-specific thalassemia mutation patterns.",
    type: "website",
  },
  twitter: {
    card: "summary",
    title: "Thalassemia Sanger Sequencing Mutation Checker",
    description:
      "Upload Sanger sequencing .ab1 files and check primer-specific thalassemia mutation patterns.",
  },
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
