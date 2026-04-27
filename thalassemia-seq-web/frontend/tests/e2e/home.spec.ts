import { expect, test } from "@playwright/test";

test("homepage renders key controls", async ({ page }) => {
  await page.goto("/");

  await expect(page.getByRole("heading", { name: "Thalassemia Sanger Sequencing Mutation Checker" })).toBeVisible();
  await expect(page.getByLabel("Upload `.ab1` file")).toBeVisible();
  await expect(page.getByLabel("Primer / Target group")).toBeVisible();

  const analyzeButton = page.getByRole("button", { name: "Analyze" });
  await expect(analyzeButton).toBeDisabled();
  await expect(page.getByText("Upload a `.ab1` file to enable Analyze.")).toBeVisible();

  await expect(page.getByRole("button", { name: "Load demo result" })).toBeEnabled();
});

test("demo mode loads and displays result panels", async ({ page }) => {
  await page.route("**/examples/demo-result.json", async (route) => {
    await route.fulfill({
      status: 200,
      contentType: "application/json",
      body: JSON.stringify({
        ok: true,
        file_name: "demo-sample.ab1",
        primer_type: "T0128",
        qc: {
          sequence_length: 128,
          average_quality: 31.4,
          low_quality_regions: [],
          warnings: [],
        },
        analysis: {
          primer_type: "T0128",
          sequence_length: 128,
          mutations: [
            {
              name: "WS",
              status: "WT",
              position: 24,
              matched_pattern: "CGCCTCCC",
              quality_score: 18,
              confidence: "high",
              notes: "Legacy single-site threshold rule.",
            },
          ],
          warnings: [],
        },
        report: {
          warnings: [],
          disclaimer:
            "This tool is for educational/research workflow support only and must not be used as a standalone clinical diagnostic tool.",
        },
      }),
    });
  });

  await page.goto("/");

  await page.getByRole("button", { name: "Load demo result" }).click();

  await expect(page.getByRole("heading", { name: "Result Summary" })).toBeVisible();
  await expect(page.getByText("File").first()).toBeVisible();
  await expect(page.getByText("demo-sample.ab1")).toBeVisible();

  await expect(page.getByRole("heading", { name: "Quality Control" })).toBeVisible();
  await expect(page.getByRole("heading", { name: "Mutation Results" })).toBeVisible();
  await expect(page.getByRole("button", { name: "Download JSON report" })).toBeVisible();
});
