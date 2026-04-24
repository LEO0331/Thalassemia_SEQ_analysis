import "./globals.css";
import type { Metadata } from "next";
import { IBM_Plex_Mono, Manrope, Playfair_Display } from "next/font/google";
import React from "react";

const display = Playfair_Display({
  subsets: ["latin"],
  variable: "--font-display",
  weight: ["600", "700"],
});

const body = Manrope({
  subsets: ["latin"],
  variable: "--font-body",
  weight: ["400", "500", "600", "700"],
});

const mono = IBM_Plex_Mono({
  subsets: ["latin"],
  variable: "--font-mono",
  weight: ["400", "500"],
});

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
    <html lang="en" className={`${display.variable} ${body.variable} ${mono.variable}`}>
      <body>{children}</body>
    </html>
  );
}
