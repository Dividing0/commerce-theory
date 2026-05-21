# Changelog

## 0.1.1

- Tightened validated orders so coupon amounts must fit within cart net subtotal.
- Added source-preservation predicates and theorems for cart-line, cart-line-list, and order validators.
- Strengthened logistics shipment plans with per-SKU allocation quantity matching.
- Changed shipment-plan validation to check an independently supplied destination zone.
- Made the order-event validator accept only complete shipped or refunded lifecycle words.
- Reworked domain-event replay validity preservation to inspect the replay step proof.

## 0.1.0

- Init release.
