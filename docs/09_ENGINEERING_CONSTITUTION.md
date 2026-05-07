# Engineering Constitution

This constitution is binding guidance for future development of `Sacramento Investor Radar` and the monthly market mailer. Before changing product behavior, scoring, source ingestion, dashboard UX, report outputs, or email automation, read this file and make the change consistent with it.

## Article 1: The Product Serves Investor Judgment

The product exists to improve investor research, not to create impressive charts.

Every feature must help answer at least one question:

- Where should I focus?
- Why is that area interesting?
- What evidence supports the signal?
- What could make the signal wrong?
- What should I verify manually?

Features that do not answer one of these questions should not be built yet.

## Article 2: Never Hide Uncertainty

The product must show uncertainty next to opportunity.

Required for every ranked market or ZIP:

- Confidence score or confidence label.
- Quality flags.
- Source coverage.
- Population or market-size context when available.
- Caveats for extreme movement, short history, low volume, and source disagreement.

If a metric looks amazing but may be bad data, the warning belongs beside the metric, not buried in methodology.

## Article 3: No Fake Precision

The product must not pretend to know more than the data supports.

Do not publish:

- Buy/sell recommendations.
- Guaranteed return language.
- Appraisal-style claims.
- Overly precise opportunity rankings without caveats.
- Single-source extreme spikes as strong signals.

Use language like:

- Watchlist candidate.
- Research signal.
- Worth investigating.
- Needs manual verification.
- Low-confidence spike.

## Article 4: Preserve Source Truth

Raw data must be preserved before transformation whenever possible.

Each source snapshot should record:

- Source URL.
- Retrieval timestamp.
- Snapshot month.
- Checksum.
- Row count.
- Column list.
- Known source limitations.

Never overwrite raw data with cleaned data.

## Article 5: Use Layered Data Architecture

The project should move toward Bronze, Silver, and Gold layers:

- Bronze: raw source snapshots.
- Silver: normalized and validated tables.
- Gold: investor-ready marts for reports, dashboards, and alerts.

Reports and dashboards should read from Gold outputs, not repeat complex transformations in the presentation layer.

## Article 6: Quality Gates Come Before Rankings

Quality checks must run before rankings are published.

Critical failures block affected outputs:

- Missing required columns.
- Empty source file.
- Broken date parsing.
- Broken geography keys.
- Current report built from stale data without a clear label.

Warnings may allow rows through, but the warning must be visible:

- Extreme rent/value movement.
- Short history.
- Small population or market size.
- High volatility.
- Source disagreement.
- Heavy new supply pressure.

## Article 7: Source Agreement Beats Source Worship

No single source is sacred.

When multiple sources exist, compare them. If they disagree, reduce confidence and show the disagreement. Do not silently pick the source that makes the chart look better.

Priority comparisons:

- Zillow rent trends versus Apartment List rent trends.
- Zillow/Redfin/Realtor value or listing signals when available.
- City permit data versus county permit data versus Census permit data.
- Population-normalized metrics versus raw counts.

## Article 8: Local Context Matters

The Sacramento product must stay locally useful.

Permit signals must distinguish:

- New residential supply.
- ADUs and conversions.
- Remodels and additions.
- Maintenance and repair.
- Roofing, HVAC, plumbing, electrical.
- Solar, batteries, EV work.
- Site preparation, grading, framing, foundation.

Do not call all renovation activity gentrification. Describe the actual work type.

## Article 9: Email Is The Front Door

The email brief is the first product surface. The dashboard is the research room.

Build in this order unless real user demand proves otherwise:

1. Free monthly issue.
2. Paid monthly brief.
3. Dashboard research room.
4. Watchlist alerts.
5. California expansion.

Do not overbuild dashboard features before the email list produces replies and paid intent.

## Article 10: Explain Every Score

Scores must be transparent and versioned.

Every score should include:

- Score version.
- Input metrics.
- Weighting logic or plain-English formula.
- Confidence score.
- Quality flags.
- Source coverage.
- Computed timestamp.

If a user cannot understand why a ZIP ranked high, the score is not ready.

## Article 11: Build For Auditability

Every monthly run should be reproducible enough to explain later.

Required run outputs:

- Source manifest.
- Validation summary.
- Generated charts list.
- Generated CSV list.
- Quarantined rows summary.
- Email send or dry-run status.
- State update status.

Dry runs must never update `state/_last_sent.json`.

## Article 12: Configuration And Secrets Stay Out Of Code

Credentials and deploy-specific settings belong in environment variables or GitHub Secrets.

Never commit:

- Gmail app passwords.
- API keys.
- Subscriber lists.
- Private customer data.
- Local `.env` files.

The codebase should be safe to make public without exposing credentials.

## Article 13: Prefer Boring Systems Until Scale Demands More

Use simple files, GitHub Actions, and generated artifacts while the product is young.

Add databases, queues, auth systems, and paid SaaS infrastructure only when one of these is true:

- Data volume requires it.
- Paid users require it.
- Manual operations are causing errors.
- Reliability cannot be maintained with the simpler setup.

Boring and reliable beats clever and fragile.

## Article 14: Dashboard UX Must Support Repeated Research

The dashboard should feel like an investor workbench, not a landing page.

Rules:

- Put decision tables and filters near the top.
- Keep charts tied to a specific investor question.
- Let users sort and filter without losing context.
- Highlight selected map/chart rows in tables when possible.
- Keep raw evidence accessible.
- Avoid decorative UI that reduces scan speed.

## Article 15: Expansion Requires Local Data Fitness

Do not expand to a new California market just because Zillow data exists.

A new market needs:

- Reliable permit source.
- Rent and home-value coverage.
- Population normalization.
- Clear local investor demand.
- Known source limitations.
- Repeatable monthly pipeline.

If permit data is weak, label the product as rent/value radar only for that market.

## Article 16: Paid Claims Must Be Earned

Charge only when the product consistently saves users time or improves decisions.

Acceptable paid value:

- Full ZIP watchlist.
- Contractor drilldowns.
- Source-backed supply warnings.
- Watchlist alerts.
- CSV/PDF exports.
- Historical archive.

Weak paid value:

- More charts without explanation.
- Raw data dumps.
- Rankings without warnings.
- Generic national market commentary.

## Article 17: User Feedback Is Evidence, Not Orders

User requests should be logged and respected, but not blindly built.

Build when:

- Multiple users ask for the same thing.
- The request improves investor decisions.
- The data can support the claim.
- The feature can be maintained monthly.

Defer when:

- It creates legal/advice risk.
- It relies on weak data.
- It distracts from Sacramento traction.
- It adds complexity before demand.

## Article 18: Every Change Must State Its Product Reason

Any meaningful change should be able to say:

- What investor question does this answer?
- What data source supports it?
- What quality checks protect it?
- What output changes?
- What could go wrong?

If those answers are unclear, pause before building.

## Constitution Check For Future Work

Before adding a feature, answer:

```text
Investor question:
Data source:
Data quality gate:
Confidence/warning behavior:
Report/dashboard output:
Manual verification note:
Maintenance cost:
```

Before changing a score, answer:

```text
Score name:
Current version:
New version:
Reason for change:
Inputs added/removed:
Expected ranking impact:
Backtest or sample comparison:
Warnings affected:
```

Before adding a source, answer:

```text
Source name:
Source URL:
Owner/publisher:
Coverage:
Refresh frequency:
License/public-use notes:
Required fields:
Known limitations:
Quality gates:
Fallback behavior:
```
