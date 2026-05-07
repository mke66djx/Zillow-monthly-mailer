# Zillow Monthly Emailer

Monthly GitHub Actions mailer for Zillow Research market charts.

The workflow checks Zillow's published CSV month before sending. It only sends when Zillow's latest month advances beyond `state/_last_sent.json`, unless a manual run uses `force_send`.

## What It Sends

- Existing county-vs-metro ZHVI/ZORI overlays for the monitored areas.
- Existing top/bottom ZIP trend charts for each monitored metro.
- Existing ZIP heatmaps and detailed CSV attachments.
- National ZIP investment scanner outputs:
  - Top cash-flow opportunity ZIPs.
  - Rent growth leaders.
  - Home value growth leaders.
  - Rent momentum slowdown list.
  - Rent growth versus home value growth scatter.
- Monitored-area ZIP opportunity charts and CSVs for the areas in `AREAS`.
- Sacramento permit intelligence:
  - ZIP supply and renovation summaries.
  - Contractor rollups.
  - Site-level permit CSV with address, site location, contractor, work phase, project, and work description.

## GitHub Actions

The scheduled workflow runs daily and sends only when a new Zillow month is detected.

Manual workflow inputs:

- `force_send`: bypasses the month guard and sends now.
- `dry_run`: generates charts/CSVs but does not send email or update state.
- `skip_heatmaps`: skips GeoPandas heatmaps for faster manual testing.

Generated outputs are uploaded as a GitHub Actions artifact named `zillow-monthly-output`.

## Required Secret

Set this repository secret:

```text
GMAIL_APP_PWD
```

## Local Dry Run

From the repo folder:

```powershell
$env:DRY_RUN="1"
$env:FORCE_SEND="1"
$env:SKIP_HEATMAPS="1"
python zillow_monthly_emailer.py
```

Outputs are written to:

```text
ZillowMonthly
```

## Product Launch Docs

This branch also includes a first product plan for turning the monthly market pipeline into `Sacramento Investor Radar`, starting with an email list and growing into a paid California investor dashboard.

- [Executable launch plan](docs/01_EXECUTABLE_LAUNCH_PLAN.md)
- [Landing page and email copy](docs/02_LANDING_PAGE_AND_EMAIL_KIT.md)
- [Report and dashboard product spec](docs/03_REPORT_AND_DASHBOARD_SPEC.md)
- [30-day content calendar](docs/04_CONTENT_CALENDAR_30_DAYS.csv)
- [First issue runbook](docs/05_FIRST_ISSUE_RUNBOOK.md)

## Product System Docs

These files define how the product should be built from here forward. Read the constitution before changing product behavior, scoring, data quality, source ingestion, dashboard UX, or mailer outputs.

- [Operating flow](docs/06_OPERATING_FLOW.md)
- [Product blueprint](docs/07_PRODUCT_BLUEPRINT.md)
- [Reference architecture](docs/08_REFERENCE_ARCHITECTURE.md)
- [Engineering constitution](docs/09_ENGINEERING_CONSTITUTION.md)
