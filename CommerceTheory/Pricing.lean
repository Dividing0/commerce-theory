import CommerceTheory.Inventory

namespace CommerceTheory

/-! ## 3. Cart, pricing, coupons, shipping, tax, and order totals -/

/-!
Pricing code separates line-level arithmetic from order-level arithmetic. The
main invariant is that discounts never make net totals exceed gross totals.
Those facts are then reused to prove that a complete order total is bounded by
gross cart value plus shipping and tax.
-/

/-- One cart line with enough data to compute revenue, cost, discount, and weight. -/
structure CartLine where
  sku : Sku
  price : Money
  cost : Money
  quantity : Quantity
  discount : Money
  weight : Weight
  discount_le_gross : discount ≤ price * quantity

/-- Unit sale price times quantity before discounts. -/
def lineGrossTotal (line : CartLine) : Money :=
  line.price * line.quantity

/-- Unit cost times quantity, used by profit-oriented modules. -/
def lineCostTotal (line : CartLine) : Money :=
  line.cost * line.quantity

/-- Gross total after subtracting the line discount. -/
def lineNetTotal (line : CartLine) : Money :=
  lineGrossTotal line - line.discount

/-- Computes or checks `lineWeightTotal` using the validated data in this module. -/
def lineWeightTotal (line : CartLine) : Weight :=
  line.weight * line.quantity

/-- States the safety property captured by `lineNetTotal_le_grossTotal`. -/
theorem lineNetTotal_le_grossTotal (line : CartLine) :
    lineNetTotal line ≤ lineGrossTotal line := by
  unfold lineNetTotal
  exact Nat.sub_le (lineGrossTotal line) line.discount

/-- States the safety property captured by `lineNet_plus_discount_eq_gross`. -/
theorem lineNet_plus_discount_eq_gross (line : CartLine) :
    lineNetTotal line + line.discount = lineGrossTotal line := by
  unfold lineNetTotal
  exact Nat.sub_add_cancel line.discount_le_gross

/-- States the safety property captured by `lineCost_le_gross_if_unit_cost_le_price`. -/
theorem lineCost_le_gross_if_unit_cost_le_price
    (line : CartLine) (h : line.cost ≤ line.price) :
    lineCostTotal line ≤ lineGrossTotal line := by
  unfold lineCostTotal
  unfold lineGrossTotal
  exact Nat.mul_le_mul_right line.quantity h

/-- Computes or checks `cartGrossTotal` using the validated data in this module. -/
def cartGrossTotal : List CartLine → Money
  | [] => 0
  | line :: rest => lineGrossTotal line + cartGrossTotal rest

/-- Computes or checks `cartNetTotal` using the validated data in this module. -/
def cartNetTotal : List CartLine → Money
  | [] => 0
  | line :: rest => lineNetTotal line + cartNetTotal rest

/-- Computes or checks `cartDiscountTotal` using the validated data in this module. -/
def cartDiscountTotal : List CartLine → Money
  | [] => 0
  | line :: rest => line.discount + cartDiscountTotal rest

/-- Computes or checks `cartWeightTotal` using the validated data in this module. -/
def cartWeightTotal : List CartLine → Weight
  | [] => 0
  | line :: rest => lineWeightTotal line + cartWeightTotal rest

/-- Computes or checks `cartQuantityTotal` using the validated data in this module. -/
def cartQuantityTotal : List CartLine → Quantity
  | [] => 0
  | line :: rest => line.quantity + cartQuantityTotal rest

/-- Cart-level version of the line invariant: net total cannot exceed gross. -/
theorem cartNetTotal_le_grossTotal (items : List CartLine) :
    cartNetTotal items ≤ cartGrossTotal items := by
  induction items with
  | nil =>
      simp [cartNetTotal, cartGrossTotal]
  | cons line rest ih =>
      have hline : lineNetTotal line ≤ lineGrossTotal line :=
        lineNetTotal_le_grossTotal line
      simpa [cartNetTotal, cartGrossTotal] using Nat.add_le_add hline ih

/-- Cart-level conservation law: net plus discounts recovers gross. -/
theorem cartNetTotal_plus_discountTotal_eq_grossTotal (items : List CartLine) :
    cartNetTotal items + cartDiscountTotal items = cartGrossTotal items := by
  induction items with
  | nil =>
      simp [cartNetTotal, cartDiscountTotal, cartGrossTotal]
  | cons line rest ih =>
      have hline := lineNet_plus_discount_eq_gross line
      calc
        cartNetTotal (line :: rest) + cartDiscountTotal (line :: rest)
            = (lineNetTotal line + line.discount) +
                (cartNetTotal rest + cartDiscountTotal rest) := by
              simp [cartNetTotal, cartDiscountTotal]
              ac_rfl
        _ = lineGrossTotal line + cartGrossTotal rest := by
              rw [hline, ih]
        _ = cartGrossTotal (line :: rest) := by
              simp [cartGrossTotal]

/-- Total discounts never exceed the undiscounted cart gross. -/
theorem cartDiscountTotal_le_grossTotal (items : List CartLine) :
    cartDiscountTotal items ≤ cartGrossTotal items := by
  induction items with
  | nil =>
      simp [cartDiscountTotal, cartGrossTotal]
  | cons line rest ih =>
      simpa [cartDiscountTotal, cartGrossTotal, lineGrossTotal] using
        Nat.add_le_add line.discount_le_gross ih

/-- Data shape for `Coupon`; proof fields record invariants when needed. -/
structure Coupon where
  amount : Money
  minSubtotal : Money
  maxUses : Nat

/-- A coupon is applicable only when both subtotal and usage constraints pass. -/
def couponCanBeApplied (coupon : Coupon) (subtotal : Money) (usesBefore : Nat) : Prop :=
  coupon.minSubtotal ≤ subtotal ∧ usesBefore < coupon.maxUses

/-- States the safety property captured by `coupon_application_meets_min_subtotal`. -/
theorem coupon_application_meets_min_subtotal
    (coupon : Coupon) (subtotal : Money) (usesBefore : Nat)
    (h : couponCanBeApplied coupon subtotal usesBefore) :
    coupon.minSubtotal ≤ subtotal := by
  exact h.left

/-- Applying a coupon also proves the usage count is still below its cap. -/
theorem coupon_application_usage_below_max
    (coupon : Coupon) (subtotal : Money) (usesBefore : Nat)
    (h : couponCanBeApplied coupon subtotal usesBefore) :
    usesBefore < coupon.maxUses := by
  exact h.right

/-- Computes or checks `subtotalAfterCouponAmount` using the validated data in this module. -/
def subtotalAfterCouponAmount (subtotal couponAmount : Money) : Money :=
  subtotal - couponAmount

/-- States the safety property captured by `subtotalAfterCouponAmount_le_subtotal`. -/
theorem subtotalAfterCouponAmount_le_subtotal (subtotal couponAmount : Money) :
    subtotalAfterCouponAmount subtotal couponAmount ≤ subtotal := by
  unfold subtotalAfterCouponAmount
  exact Nat.sub_le subtotal couponAmount

/-- Computes or checks `orderSubtotal` using the validated data in this module. -/
def orderSubtotal (items : List CartLine) (couponAmount : Money) : Money :=
  subtotalAfterCouponAmount (cartNetTotal items) couponAmount

/-- States the safety property captured by `orderSubtotal_le_cartGrossTotal`. -/
theorem orderSubtotal_le_cartGrossTotal (items : List CartLine) (couponAmount : Money) :
    orderSubtotal items couponAmount ≤ cartGrossTotal items := by
  unfold orderSubtotal
  have h1 : subtotalAfterCouponAmount (cartNetTotal items) couponAmount ≤ cartNetTotal items :=
    subtotalAfterCouponAmount_le_subtotal (cartNetTotal items) couponAmount
  have h2 : cartNetTotal items ≤ cartGrossTotal items :=
    cartNetTotal_le_grossTotal items
  exact h1.trans h2

/-- Data shape for `ShippingMethod`; proof fields record invariants when needed. -/
structure ShippingMethod where
  price : Money
  freeThreshold : Money
  maxWeight : Weight

/-- Shipping can be selected only when the cart weight fits the method. -/
def shippingAvailable (method : ShippingMethod) (weight : Weight) : Prop :=
  weight ≤ method.maxWeight

/-- Shipping is either free after the threshold or the method's configured price. -/
def shippingCharge (method : ShippingMethod) (subtotal : Money) : Money :=
  if method.freeThreshold ≤ subtotal then 0 else method.price

/-- States the safety property captured by `shippingCharge_le_method_price`. -/
theorem shippingCharge_le_method_price (method : ShippingMethod) (subtotal : Money) :
    shippingCharge method subtotal ≤ method.price := by
  unfold shippingCharge
  by_cases h : method.freeThreshold ≤ subtotal
  · simp [h]
  · simp [h]

/-- States the safety property captured by `shipping_is_free_when_threshold_reached`. -/
theorem shipping_is_free_when_threshold_reached
    (method : ShippingMethod) (subtotal : Money)
    (h : method.freeThreshold ≤ subtotal) :
    shippingCharge method subtotal = 0 := by
  unfold shippingCharge
  simp [h]

/-- Shipping falls back to the configured method price before the free threshold. -/
theorem shippingCharge_eq_price_when_below_threshold
    (method : ShippingMethod) (subtotal : Money)
    (h : ¬ method.freeThreshold ≤ subtotal) :
    shippingCharge method subtotal = method.price := by
  unfold shippingCharge
  simp [h]

/-- Computes or checks `orderTotal` using the validated data in this module. -/
def orderTotal
    (method : ShippingMethod)
    (couponAmount tax : Money)
    (items : List CartLine) : Money :=
  let subtotal := orderSubtotal items couponAmount
  subtotal + shippingCharge method subtotal + tax

/-- The total cannot exceed undiscounted cart gross plus maximum shipping and tax. -/
theorem orderTotal_le_gross_plus_shipping_plus_tax
    (method : ShippingMethod)
    (couponAmount tax : Money)
    (items : List CartLine) :
    orderTotal method couponAmount tax items ≤
      cartGrossTotal items + method.price + tax := by
  unfold orderTotal
  have hsubtotal : orderSubtotal items couponAmount ≤ cartGrossTotal items :=
    orderSubtotal_le_cartGrossTotal items couponAmount
  have hshipping : shippingCharge method (orderSubtotal items couponAmount) ≤ method.price :=
    shippingCharge_le_method_price method (orderSubtotal items couponAmount)
  exact Nat.add_le_add (Nat.add_le_add hsubtotal hshipping) (Nat.le_refl tax)


end CommerceTheory
