import CommerceTheory.EventSourcing
import CommerceTheory.OpportunityPortfolio

namespace CommerceTheory

/-! ## Cross-module implicit invariants made explicit -/

/-!
Several domain records intentionally stay lightweight so individual modules can
be composed freely. This module adds reusable wrappers for assumptions that
cross those module boundaries: coupon caps, payment/order matching, event-stream
cursors, catalog publishability, experiment weights, and distributor sourcing.
-/

/-! ### Pricing and payment joins -/

/-- A coupon application that is both eligible and bounded by the subtotal. -/
structure BoundedCouponApplication where
  coupon : Coupon
  subtotal : Money
  usesBefore : Nat
  applicable : couponCanBeApplied coupon subtotal usesBefore
  amount_le_subtotal : coupon.amount ≤ subtotal

/-- Bounded coupon applications still satisfy the configured subtotal floor. -/
theorem boundedCoupon_application_meets_min_subtotal
    (application : BoundedCouponApplication) :
    application.coupon.minSubtotal ≤ application.subtotal := by
  exact application.applicable.left

/-- Bounded coupon applications still satisfy the configured usage cap. -/
theorem boundedCoupon_application_usage_below_max
    (application : BoundedCouponApplication) :
    application.usesBefore < application.coupon.maxUses := by
  exact application.applicable.right

/-- The discount amount of a bounded coupon fits inside the subtotal it is applied to. -/
theorem boundedCoupon_amount_le_subtotal
    (application : BoundedCouponApplication) :
    application.coupon.amount ≤ application.subtotal := by
  exact application.amount_le_subtotal

/-- Applying a bounded coupon conserves the original subtotal. -/
theorem boundedCoupon_subtotalAfter_add_amount_eq_subtotal
    (application : BoundedCouponApplication) :
    subtotalAfterCouponAmount application.subtotal application.coupon.amount +
      application.coupon.amount = application.subtotal := by
  unfold subtotalAfterCouponAmount
  exact Nat.sub_add_cancel application.amount_le_subtotal

/-- A captured payment paired with the exact order id, amount, and currency it settles. -/
structure CapturedPaymentMatchesOrder where
  order : Order
  payment : CapturedPayment
  order_matches : payment.orderId = order.id
  amount_matches : payment.amount = order.total
  currency_matches : payment.currency = order.currency

/-- Matched captured payments point at their validated order. -/
theorem capturedPaymentMatchesOrder_order_id
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.orderId = matchEvidence.order.id := by
  exact matchEvidence.order_matches

/-- Matched captured payments carry exactly the order total. -/
theorem capturedPaymentMatchesOrder_amount
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.amount = matchEvidence.order.total := by
  exact matchEvidence.amount_matches

/-- Matched captured payments use the order currency. -/
theorem capturedPaymentMatchesOrder_currency
    (matchEvidence : CapturedPaymentMatchesOrder) :
    matchEvidence.payment.currency = matchEvidence.order.currency := by
  exact matchEvidence.currency_matches

/-! ### Event-stream cursor validation -/

/-- Fold the last event sequence out of an event list, starting from a default cursor. -/
def eventStreamLastSequenceFrom : Nat → List EventEnvelope → Nat
  | last, [] => last
  | _, event :: rest => eventStreamLastSequenceFrom event.sequence rest

/-- The cursor implied by replaying an event stream from sequence zero. -/
def eventStreamComputedLastSequence (stream : EventStream) : Nat :=
  eventStreamLastSequenceFrom 0 stream.events

/-- An event stream whose ordering and stored cursor have both been validated. -/
structure ValidEventStream where
  stream : EventStream
  sequences_strict : streamSequencesStrictlyIncrease stream
  lastSequence_correct : stream.lastSequence = eventStreamComputedLastSequence stream

/-- Valid event streams expose strict sequence ordering. -/
theorem validEventStream_sequences_strict (stream : ValidEventStream) :
    streamSequencesStrictlyIncrease stream.stream := by
  exact stream.sequences_strict

/-- Valid event streams expose that the stored cursor is the computed last sequence. -/
theorem validEventStream_lastSequence_correct (stream : ValidEventStream) :
    stream.stream.lastSequence = eventStreamComputedLastSequence stream.stream := by
  exact stream.lastSequence_correct

/-- The first event in a nonempty valid stream must be newer than sequence zero. -/
theorem validEventStream_first_sequence_positive
    (stream : ValidEventStream) (event : EventEnvelope) (rest : List EventEnvelope)
    (hEvents : stream.stream.events = event :: rest) :
    0 < event.sequence := by
  have hStrict : streamSequencesStrictlyIncreaseFrom 0 (event :: rest) := by
    have hOrdered := stream.sequences_strict
    unfold streamSequencesStrictlyIncrease at hOrdered
    rw [← hEvents]
    exact hOrdered
  exact streamSequencesStrictlyIncreaseFrom_head 0 event rest hStrict

/-! ### Catalog, marketplace, and feed publishability -/

/-- Active catalog products are the only products eligible for sale. -/
def productActive (product : Product) : Prop :=
  product.status = ProductStatus.Active

/-- Active variants are the only variants eligible for sale. -/
def variantActive (variant : ProductVariant) : Prop :=
  variant.active = true

/-- A catalog entry whose product and variant are both sellable. -/
structure SellableCatalogEntry where
  entry : ProductCatalogEntry
  product_active : productActive entry.product
  variant_active : variantActive entry.variant

/-- Sellable catalog entries still preserve product/variant identity. -/
theorem sellableCatalogEntry_variant_belongs_to_product
    (entry : SellableCatalogEntry) :
    entry.entry.variant.productId = entry.entry.product.id := by
  exact entry.entry.variant_belongs_to_product

/-- Sellable catalog entries expose that the product is active. -/
theorem sellableCatalogEntry_product_active (entry : SellableCatalogEntry) :
    entry.entry.product.status = ProductStatus.Active := by
  exact entry.product_active

/-- Sellable catalog entries expose that the variant is active. -/
theorem sellableCatalogEntry_variant_active (entry : SellableCatalogEntry) :
    entry.entry.variant.active = true := by
  exact entry.variant_active

/-- Feed lines with positive published stock. -/
def feedLineHasStock (line : SafeProductFeedLine) : Prop :=
  0 < line.stock

/-- A feed line that is safe and publishable because it has stock. -/
structure PublishableFeedLine where
  line : SafeProductFeedLine
  has_stock : feedLineHasStock line

/-- Publishable feed lines preserve SKU identity with the stock source. -/
theorem publishableFeedLine_same_sku (line : PublishableFeedLine) :
    line.line.sku = line.line.stockState.sku := by
  exact line.line.same_sku

/-- Publishable feed lines keep price inside the channel policy. -/
theorem publishableFeedLine_price_valid (line : PublishableFeedLine) :
    line.line.pricePolicy.minPrice ≤ line.line.price ∧
      line.line.price ≤ line.line.pricePolicy.maxPrice := by
  exact line.line.price_valid

/-- Publishable feed lines expose their positive stock guarantee. -/
theorem publishableFeedLine_stock_positive (line : PublishableFeedLine) :
    0 < line.line.stock := by
  exact line.has_stock

/-- Publishable feed lines imply the source stock has positive available quantity. -/
theorem publishableFeedLine_available_positive (line : PublishableFeedLine) :
    0 < availableStock line.line.stockState := by
  exact lt_of_lt_of_le line.has_stock line.line.stock_safe

/-! ### Experiment and distributor sourcing guards -/

/-- Any variant in a traffic list has weight no larger than the list total. -/
theorem experimentVariant_trafficWeight_le_total
    (variant : ExperimentVariant) (variants : List ExperimentVariant)
    (hmem : variant ∈ variants) :
    variant.trafficWeight ≤ experimentTrafficTotal variants := by
  induction variants with
  | nil =>
      cases hmem
  | cons head rest ih =>
      simp [experimentTrafficTotal] at hmem ⊢
      rcases hmem with h | h
      · rw [h]
        exact Nat.le_add_right head.trafficWeight (experimentTrafficTotal rest)
      · exact (ih h).trans
          (Nat.le_add_left (experimentTrafficTotal rest) head.trafficWeight)

/-- Every variant in a validated experiment has traffic weight at most 100. -/
theorem experimentVariant_trafficWeight_le_100
    (experiment : Experiment) (variant : ExperimentVariant)
    (hmem : variant ∈ experiment.variants) :
    variant.trafficWeight ≤ 100 := by
  rw [← experiment.traffic_total_100]
  exact experimentVariant_trafficWeight_le_total variant experiment.variants hmem

/-- Active distributor products are eligible for sourcing. -/
def distributorProductActive (product : DistributorProduct) : Prop :=
  product.active = true

/-- A distributor product can source a quantity when it is active and within its bounds. -/
def distributorProductCanSource (product : DistributorProduct) (units : Quantity) : Prop :=
  distributorProductActive product ∧ product.minOrderQty ≤ units ∧ units ≤ product.availableQty

/-- A distributor product paired with a sourceable quantity. -/
structure SourceableDistributorProduct where
  product : DistributorProduct
  units : Quantity
  can_source : distributorProductCanSource product units

/-- Sourceable distributor products are active. -/
theorem sourceableDistributorProduct_active
    (source : SourceableDistributorProduct) :
    source.product.active = true := by
  exact source.can_source.left

/-- Sourceable quantities satisfy the distributor minimum order quantity. -/
theorem sourceableDistributorProduct_min_order
    (source : SourceableDistributorProduct) :
    source.product.minOrderQty ≤ source.units := by
  exact source.can_source.right.left

/-- Sourceable quantities fit inside the distributor's available quantity. -/
theorem sourceableDistributorProduct_available
    (source : SourceableDistributorProduct) :
    source.units ≤ source.product.availableQty := by
  exact source.can_source.right.right

end CommerceTheory
