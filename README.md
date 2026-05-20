# Commerce Theory

Lean 4 / Mathlib specification for an e-commerce and marketplace domain.

The project models business invariants for catalog data, inventory, pricing,
orders, payments, accounting, marketplaces, marketing, B2B, dropshipping,
competitor pricing, risk, privacy, event sourcing, post-purchase flows, and
opportunity selection.

The code is intentionally domain-focused. It does not model HTTP, SQL, UI, or
spreadsheet IO. Instead, it defines validated structures and proves small safety
theorems that an implementation can mirror with private fields, smart
constructors, and tests.

## Toolchain

- Lean: `leanprover/lean4:v4.29.1`
- Lake package: `commerce-theory`
- Dependency: `leanprover-community/mathlib`, pinned to `v4.29.1`

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
- `CommerceTheory/PostPurchase.lean`: subscriptions, gift cards, chargebacks, and
  cashflow plans.
- `CommerceTheory/Forecasting.lean`: forecast confidence, replenishment gates,
  supplier quality metrics, and supplier risk policy.
- `CommerceTheory/OpportunityPortfolio.lean`: dropship opportunity candidates,
  portfolio capital limits, and minimum-profit constraints.
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

Functions that change state usually require proofs as arguments and return new
validated structures. Theorems then expose the reusable guarantees, such as:

- order totals stay below gross cart value plus maximum shipping and tax;
- reserved inventory never exceeds total inventory;
- refunds never exceed captured payments;
- marketplace payouts never exceed gross marketplace revenue;
- dropship offers preserve their stated minimum profit.

## Notes

The theory uses `Nat` for money and quantities, so subtraction floors at zero.
That keeps the formal model conservative and simple. Production systems can
replace these aliases with richer numeric types while preserving the same
invariants.
