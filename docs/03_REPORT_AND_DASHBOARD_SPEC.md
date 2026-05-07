# Report And Dashboard Product Spec

## Product Rule

The email report is the product front door. The dashboard is the paid research room.

Do not lead with raw tables. Lead with decisions:

- Where to look.
- Why it matters.
- What changed.
- What might be wrong.
- What to verify manually.

## Monthly Report Structure

### 1. Executive Summary

Length: 5 bullets.

Required bullets:

- Best ZIP signal this month.
- Strongest rent/value gap.
- Strongest rent growth.
- Biggest supply risk.
- Most notable contractor or permit movement.

Example format:

> 95820 remains interesting because rents are rising while values are still soft, permit supply is not among the highest, and renovation activity is elevated. Confidence is medium-high. Check block-level comps before acting.

### 2. Top ZIP Opportunities

Columns:

- ZIP
- Rent YoY
- Value YoY
- Rent/value gap
- Gross yield proxy
- Confidence
- Permit supply label
- Reinvestment label
- Thesis

Ranking basis:

- Gross yield proxy.
- Rent/value gap.
- Rent YoY.
- Low/moderate value growth.
- Confidence score.
- Supply pressure penalty.

### 3. Supply Watch

Columns:

- ZIP
- New residential permits
- New units
- New residential valuation
- Units per 1k population, when population is available
- Supply pressure label
- Interpretation

Interpretation examples:

- "High new-unit activity. Good for builders, but may pressure future rents."
- "Low new supply. Rent growth may have less near-term supply pressure."
- "Large project activity. Treat ZIP-level signal separately from submarket-specific supply."

### 4. Renovation And Reinvestment Pulse

Columns:

- ZIP
- Renovation/improvement permits
- Renovation valuation
- ADU/conversion permits
- Roofing/HVAC/electrical/plumbing counts
- Reinvestment label

Important rule:

Do not call all maintenance gentrification. Separate:

- ADU/conversion.
- Remodel/addition.
- Foundation/framing.
- Roofing/HVAC/plumbing/electrical.
- Solar/battery/EV.
- Code/housing repair.

### 5. Contractor Radar

Sections:

- Top builders by new supply permits.
- Top contractors by renovation/improvement permits.
- Top contractors by ZIP footprint.
- Notable contractors entering or increasing in a ZIP.

Columns:

- Contractor
- Permit count
- New supply permits
- Renovation/improvement permits
- Housing units
- Valuation
- ZIPs
- Top work phases
- Latest permit date

### 6. Warning List

Warnings:

- Extreme rent YoY.
- Extreme value YoY.
- Low confidence.
- Short history.
- Small market proxy.
- High recent volatility.
- Heavy new supply.
- Rent momentum slowdown.
- Source disagreement, when cross-source rent data exists.

### 7. Manual Verification Checklist

For every highlighted ZIP:

- Check actual rental listings.
- Check sold comps.
- Check current active listings.
- Check pending/DOM if available.
- Check neighborhood/block differences.
- Check permit details for large one-off projects.
- Check local regulation/rent control exposure.
- Check insurance/property tax assumptions.

## Dashboard V1

Default page:

Sacramento Investor Radar

Primary navigation:

1. ZIP Radar
2. ZIP Thesis
3. Supply Watch
4. Contractor Radar
5. Reinvestment Pulse
6. Evidence / Raw Data

Remove or hide broad lab-style tabs for public users until the interface is cleaner.

## Dashboard Page Specs

### ZIP Radar

Purpose:

Find the best ZIPs to investigate.

Controls:

- Sort by cash-flow score, rent/value gap, rent growth, gross yield, confidence.
- Filter by supply pressure.
- Filter by confidence.
- Filter by minimum population.

Visuals:

- Bubble scatter: value YoY vs rent YoY.
- Bubble map.
- Top ZIP table.

### ZIP Thesis

Purpose:

Explain one ZIP.

Content:

- Rent trend chart.
- Value trend chart.
- Yield proxy.
- Rent/value gap.
- Supply pressure.
- Renovation pulse.
- Top contractors.
- Confidence notes.
- Plain-English thesis.
- Manual verification checklist.

### Supply Watch

Purpose:

Spot where new development may change the rental equation.

Content:

- New units by ZIP.
- New residential permit count.
- New residential valuation.
- Large projects.
- Work phase breakdown.

### Contractor Radar

Purpose:

Track who is active and what they are doing.

Content:

- Contractor leaderboard.
- Contractor detail view.
- ZIP footprint.
- Work phase mix.
- Recent projects.
- Site-level permits.

### Reinvestment Pulse

Purpose:

Track renovation, ADU, and improvement activity that might signal neighborhood change.

Content:

- Renovation permits by ZIP.
- ADU/conversion permits by ZIP.
- Remodel/addition permits.
- Roofing/HVAC/electrical/plumbing support signals.
- Valuation by work phase.

### Evidence / Raw Data

Purpose:

Build trust and allow manual checking.

Content:

- Source links.
- Downloadable CSVs.
- Methodology.
- Known limitations.
- Raw permit rows.

## Access Model

Free:

- Public teaser issue.
- One static sample report.

Paid Brief:

- Full email report.
- CSV downloads.
- Archived reports.

Pro:

- Dashboard login.
- ZIP thesis pages.
- Contractor drilldowns.
- Alerts/watchlist.

## Alerts Roadmap

Alert types:

- ZIP enters top 10 opportunity list.
- Rent/value gap crosses threshold.
- New supply pressure jumps.
- Renovation permits spike.
- New contractor appears in target ZIP.
- Rent slowdown warning appears.
- Confidence improves enough to trust previously suspicious ZIP.

## Product Quality Rules

- Every top pick must include confidence.
- Every extreme data move must include a warning.
- Every permit summary must separate new supply from maintenance/improvement.
- Every local supply statement must cite that permits are City of Sacramento only unless broader county data is added.
- Do not imply investment advice. Say "research signal," "watchlist candidate," or "worth investigating."
