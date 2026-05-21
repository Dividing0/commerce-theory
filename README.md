# Commerce Theory

Lean 4 / Mathlib specification for an e-commerce and marketplace domain.

The project models business invariants for catalog data, inventory, pricing,
orders, payments, accounting, marketplaces, marketing, B2B, dropshipping,
competitor pricing, risk, privacy, event sourcing, post-purchase flows, and
opportunity selection, CRM, and logistics.

## Toolchain

- Lean: `leanprover/lean4:v4.29.1`
- Lake package: `commerce-theory`
- Dependencies:
  - `leanprover-community/mathlib`, pinned to `v4.29.1`
  - `leanprover/cslib`, pinned to `v4.29.0`

## Project Layout

- `CommerceTheory/Foundation.lean`: shared units, ids, currencies, money helpers,
  basis points, and profit arithmetic.
- `CommerceTheory/Catalog.lean`: products, variants, catalog entries, listing
  content, and marketplace content policy validation.
- `CommerceTheory/Inventory.lean`: stock, reservations, optimistic locking,
  warehouse picking, packing, shipping, and allocation plans.
- `CommerceTheory/Pricing.lean`: cart lines, totals, coupons, shipping charges,
  and order-total bounds.
- `CommerceTheory/Orders.lean`: order states, payment states, typestate helpers,
  captured payments, and refund ledgers.
- `CommerceTheory/Accounting.lean`: postings, balanced journal entries, and
  payment/refund accounting projections.
- `CommerceTheory/Marketplace.lean`: marketplaces, listings, synced stock, product
  feeds, fees, payouts, and marketplace orders.
- `CommerceTheory/Marketing.lean`: campaigns, attribution, ROAS/ROI predicates,
  consent, subscriptions, and experiments.
- `CommerceTheory/B2B.lean`: retail vs wholesale modes, price books, minimum
  quantities, payment terms, and credit limits.
- `CommerceTheory/Dropshipping.lean`: suppliers, offers, reservations, purchase
  orders, SLA checks, fulfillments, and returns.
- `CommerceTheory/DropshipProfit.lean`: dropship cost models, upper bounds,
  guaranteed profit quotes, ad spend safety, and signed profit/loss.
- `CommerceTheory/CompetitorPricing.lean`: competitor offers, freshness, trust,
  price floors, undercutting, and competitor-aware dropship offers.
- `CommerceTheory/Merchandising.lean`: MAP/MSRP policy, bundles, promotion
  stacking, search results, and recommendation safety.
- `CommerceTheory/FulfillmentFinance.lean`: FX, tax, shipping zones, carrier
  quotes, package limits, and reconciliation tolerance.
- `CommerceTheory/RiskPrivacy.lean`: fraud limits, roles, actions, audit events,
  consent purposes, and processing bases.
- `CommerceTheory/EventSourcing.lean`: domain events, envelopes, streams,
  webhooks, idempotency, and state-validity preservation.
- `CommerceTheory/EventLanguage.lean`: CSLib deterministic automaton and regular
  language for coarse order-event sequence validation.
- `CommerceTheory/EventReplay.lean`: CSLib bounded step relations for webhook
  and validated system-state replay.
- `CommerceTheory/ImplicitInvariants.lean`: cross-module validated wrappers for
  assumptions such as bounded coupons, payment/order matching, event-stream
  cursors, sellable catalog entries, publishable feed lines, experiment traffic,
  sourceable distributor products, accounting projections, wholesale checkout
  authorization, fresh competitor benchmarks, currency conversion, gift-card
  expiry, chargebacks, replenishment forecasts, orderable supplier quality, and
  CRM/logistics joins.
- `CommerceTheory/PostPurchase.lean`: subscriptions, gift cards, chargebacks, and
  cashflow plans.
- `CommerceTheory/CRM.lean`: accounts, validated account/contact links, lead and
  opportunity lifecycles, currency-consistent pipelines, consent-scoped
  permitted messaging, segmentation, support cases, and retention offers.
- `CommerceTheory/Forecasting.lean`: forecast confidence, replenishment gates,
  supplier quality metrics, and supplier risk policy.
- `CommerceTheory/Logistics.lean`: eligible-order shipment plans, carrier
  handoff, tracking history with delivery scans, delivery promises, exceptions,
  warehouse transfers, and order-bound return authorizations.
- `CommerceTheory/InventoryAlgorithms.lean`: CSLib `TimeM` inventory allocation
  algorithms with explicit operation counts.
- `CommerceTheory/KeyedTotals.lean`: CSLib finite-support keyed allocation totals.
- `CommerceTheory/OpportunityPortfolio.lean`: dropship opportunity candidates,
  portfolio capital limits, and minimum-profit constraints.
- `CommerceTheory/OpportunityRanking.lean`: CSLib timed merge-sort ranking for
  dropship opportunity profit keys.
- `CommerceTheory/Workflow.lean`: CSLib labelled transition-system semantics for
  order-status workflow reachability, termination, and trace equivalence.
- `CommerceTheory/Summary.lean`: headline theorems that summarize the core safety
  guarantees.
- `CommerceTheory.lean`: library root.

## Importing

Import the whole theory:

```lean
import CommerceTheory
```

Import a focused module:

```lean
import CommerceTheory.Pricing
import CommerceTheory.Orders
import CommerceTheory.CRM
import CommerceTheory.Logistics
```

All domain declarations live in the `CommerceTheory` namespace.

## Development

After cloning or changing Lake dependencies, refresh the package graph:

```bash
lake update
```

Build the project:

```bash
lake build
```

Run the executable:

```bash
lake exe commerce-theory
```

## Modeling Pattern

Most validated structures carry proof fields. For example, an inventory state
stores `reserved_le_total`, and an order stores `total_correct`. This means a
value of the structure is not just data; it is data plus evidence that the
important business invariant already holds.

Some invariants only appear when values from multiple modules are joined. The
`ImplicitInvariants` module adds wrapper types for those cases without changing
the underlying records, so existing data shapes stay reusable while stricter
call sites can demand explicit Lean evidence.

Functions that change state usually require proofs as arguments and return new
validated structures. Theorems then expose the reusable guarantees, such as:

- order totals stay below gross cart value plus maximum shipping and tax;
- reserved inventory never exceeds total inventory;
- refunds never exceed captured payments;
- marketplace payouts never exceed gross marketplace revenue;
- dropship offers preserve their stated minimum profit;
- CRM outreach, support, retention, shipment, transfer, and return flows expose
  their permission, SLA, capacity, stock, and refund bounds.

## CSLib Integration

CSLib is most useful in this project where the commerce model already has
computer-science structure:

- Order, payment, event, and webhook lifecycles naturally fit CSLib labelled
  transition systems. `CommerceTheory.Workflow` now lifts `OrderStatus` and
  `DropshipPOStatus` transitions into `Cslib.LTS`, adding multistep reachability,
  execution evidence, terminal-state reasoning, simulation, and trace
  equivalence.
- Event replay benefits from CSLib's step-counted relations.
  `CommerceTheory.EventReplay` expresses webhook replay and valid system-state
  replay as exact/within-step relations.
- Event sequence validation can use CSLib automata and regular languages.
  `CommerceTheory.EventLanguage` models a coarse deterministic validator for
  order event words and proves the accepted language is regular.
- Opportunity scoring and selection can use CSLib algorithm proofs.
  `CommerceTheory.OpportunityRanking` now uses CSLib's timed merge sort to rank
  expected-profit keys while proving sortedness, permutation preservation,
  output length preservation, and a comparison-count bound.
- Inventory algorithms can use CSLib `TimeM` for explicit cost models.
  `CommerceTheory.InventoryAlgorithms` counts one operation per allocation row.
- Sparse business maps can use CSLib finite-support functions.
  `CommerceTheory.KeyedTotals` gives allocation quantities a finite
  warehouse/SKU support.

CSLib's automata, language, and process-calculus modules are less directly
applicable to the current domain model, but they would become useful if the
project starts modeling protocol languages, feed validators, or external API
conversation traces.

## Notes

The theory uses `Nat` for money and quantities, so subtraction floors at zero.
That keeps the formal model conservative and simple. Production systems can
replace these aliases with richer numeric types while preserving the same
invariants.
