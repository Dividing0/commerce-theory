# Changelog

## Unreleased

- Added order-aware payment replay with explicit registration, per-order refund
  authority, duplicate-placement rejection, and isolation of unrelated balances.
- Changed snapshot replay to accept event envelopes and return an updated
  snapshot, rejecting stale, duplicate, and unordered sequences.
- Proved ordering, exact cursor updates, payload correspondence, refund
  authority, order isolation, and equivalence of full and resumed replay.
- Added regression examples for cross-order refunds, cumulative refund limits,
  unknown orders, duplicate placement, sequence gaps, and snapshot resumption.
- Replaced blanket Mathlib imports with focused dependencies for practical
  domain-library builds.

## 0.1.1

- Tightened validated orders so coupon amounts must fit within cart net subtotal.
- Added source-preservation predicates and theorems for cart-line, cart-line-list, and order validators.
- Strengthened logistics shipment plans with per-SKU allocation quantity matching.
- Changed shipment-plan validation to check an independently supplied destination zone.
- Made the order-event validator accept only complete shipped or refunded lifecycle words.
- Reworked domain-event replay validity preservation to inspect the replay step proof.

## 0.1.0

- Init release.
