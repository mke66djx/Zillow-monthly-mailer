# First Issue Runbook

This is the practical checklist for launching `Sacramento Investor Radar` as an email-first product.

## Day 0 Decision

Start with email list first, not a full SaaS app.

The dashboard is valuable, but the email list proves whether investors care enough to read, reply, forward, and eventually pay. The first product is the monthly brief. The dashboard becomes the paid research room after the brief gets traction.

## Accounts To Open

Open these now:

- Beehiiv publication for email capture and monthly issues.
- Domain name for the publication.
- LinkedIn page or personal LinkedIn posting plan.
- X account only if you will actually post 3 to 5 times per week.
- Simple tracking sheet for leads, replies, beta users, and requested ZIPs.

Defer these:

- Instagram, TikTok, YouTube, podcast, Discord, and Slack community.
- Full paid dashboard login.
- Multi-city branding.
- Heavy CRM or sales automation.

Reason: the first bottleneck is trust and audience feedback, not software surface area.

## Suggested Name And Positioning

Name:

Sacramento Investor Radar

One-line positioning:

Monthly ZIP, rent, permit, and contractor intelligence for Sacramento real estate investors.

Short description:

Find where rents are moving, where values are lagging, where new supply is coming, and which contractors are active before you waste time searching the wrong ZIPs.

## Beehiiv Setup

1. Create the publication.
2. Add the name and logo placeholder.
3. Add the landing page headline from `docs/02_LANDING_PAGE_AND_EMAIL_KIT.md`.
4. Add signup fields:
   - Email
   - First name
   - Optional role
5. Create tags:
   - investor
   - agent
   - lender
   - contractor
   - property-manager
   - beta
   - wants-paid-report
6. Create the welcome email using Email 1 from `docs/02_LANDING_PAGE_AND_EMAIL_KIT.md`.
7. Add the disclaimer footer.
8. Connect the domain when ready.

## First Sample Issue

The first issue should be short enough to read and concrete enough to prove the product.

Required sections:

1. What changed this month.
2. Top 3 Sacramento ZIPs to watch.
3. One rent/value gap chart.
4. One supply pressure chart.
5. One renovation or ADU signal.
6. One contractor radar highlight.
7. Three warnings or caveats.
8. Reply ask: "Which ZIP or contractor should I watch next month?"

Do not send the full raw dashboard. Send the useful conclusion first, then offer the deeper file/report to people who reply.

## First Issue Build Steps

From the repo folder:

```powershell
$env:DRY_RUN="1"
$env:FORCE_SEND="1"
$env:SKIP_HEATMAPS="1"
python zillow_monthly_emailer.py
```

Outputs go to:

```text
ZillowMonthly
```

Use these outputs first:

- `Sacramento_zip_opportunities_dashboard.csv`
- `sacramento_permit_zip_summary.csv`
- `sacramento_top_contractors.csv`
- `sacramento_site_level_permits.csv`
- The Sacramento opportunity, permit, and contractor PNG charts.

## First Issue Editorial Rules

- Do not call something a buy signal.
- Say "watchlist candidate" or "research signal."
- Explain why a ZIP is interesting in plain English.
- Show confidence and warnings beside every eye-catching metric.
- Separate new residential supply from renovation, ADU, repair, and maintenance.
- Say clearly that City of Sacramento permit data is not the same as all Sacramento County permit data.
- End with a reply question.

## First 50 Subscribers

Start manually. This is not spam. It is direct founder research.

Target people:

- Local buy-and-hold investors.
- Small multifamily investors.
- Investor-friendly agents.
- DSCR and investor lenders.
- Property managers.
- Contractors and builders.
- Sacramento real estate meetup organizers.

Daily action for the first 10 days:

- Send 10 personal messages.
- Post 1 useful chart or insight.
- Ask 3 people for feedback on the sample issue.
- Log every reply.

Manual message:

```text
Hey, I am building a monthly Sacramento real estate investor brief that tracks ZIP-level rent growth, home value growth, building permits, renovation activity, and contractor movement.

The goal is to help investors know where to focus before looking at individual deals.

I am putting together the first free issue. Want me to send it to you?
```

## Launch Day Checklist

- Landing page is live.
- Welcome email is active.
- Sample issue is drafted.
- Charts are readable on mobile.
- Disclaimers are included.
- Top 3 ZIPs have confidence notes.
- Permit section separates new supply from renovation.
- Contractor section includes work type and ZIP footprint.
- Reply ask is included.
- 20 personal launch messages are ready.

## First Two Weeks

Week 1:

- Publish the free landing page.
- Send the first sample issue to 20 to 50 known contacts.
- Post five chart snippets.
- Ask every reader which ZIPs they care about.
- Track every requested ZIP and contractor.

Week 2:

- Publish one follow-up post using reader feedback.
- Create a beta list of people who asked for more detail.
- Offer to send the full PDF/CSV version manually.
- Ask what would make the paid report worth $19/month.
- Do not build more dashboard features unless the feedback repeats.

## When To Charge

Charge only after at least one of these is true:

- 100 email subscribers.
- 10 people reply with specific ZIP/contractor requests.
- 5 people ask for the full report.
- 3 people say they would pay for alerts, CSVs, or dashboard access.

Founding offer:

- $19/month for the paid brief.
- $149/year founding subscriber.
- Include full report, CSV downloads, and early dashboard access.

## What To Build Next

Only build features that support one of these paid reasons:

- Save investors time finding ZIPs.
- Help investors avoid bad data spikes.
- Show supply pressure before it becomes obvious.
- Track contractors and permit activity.
- Create watchlists for specific ZIPs.

Next dashboard features after email traction:

- ZIP thesis page.
- Contractor detail page.
- Watchlist alerts.
- Monthly report archive.
- CSV/PDF export for paid users.
