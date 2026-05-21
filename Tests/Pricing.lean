import CommerceTheory.Pricing

namespace CommerceTheory.Tests

def pricingSkuA : Sku :=
  { value := 4101 }

def pricingSkuB : Sku :=
  { value := 4102 }

def pricingCartLineA : CartLine :=
  { sku := pricingSkuA
    price := 1200
    cost := 700
    quantity := 3
    discount := 600
    weight := 2
    discount_le_gross := by norm_num }

def pricingCartLineB : CartLine :=
  { sku := pricingSkuB
    price := 800
    cost := 350
    quantity := 2
    discount := 0
    weight := 5
    discount_le_gross := by norm_num }

def pricingCart : List CartLine :=
  [pricingCartLineA, pricingCartLineB]

def pricingShipping : ShippingMethod :=
  { price := 750
    freeThreshold := 5000
    maxWeight := 20 }

def pricingCartTotalsPass : Bool :=
  cartGrossTotal pricingCart == 5200 &&
    cartDiscountTotal pricingCart == 600 &&
    cartNetTotal pricingCart == 4600 &&
    cartWeightTotal pricingCart == 16 &&
    cartQuantityTotal pricingCart == 5

def pricingShippingThresholdPass : Bool :=
  shippingCharge pricingShipping 4999 == 750 &&
    shippingCharge pricingShipping 5000 == 0 &&
    shippingCharge pricingShipping 6200 == 0

def pricingOrderTotalPass : Bool :=
  orderTotal pricingShipping 0 360 pricingCart == 5710 &&
    orderTotal pricingShipping 600 360 pricingCart == 5110

/-- info: true -/
#guard_msgs in
#eval pricingCartTotalsPass

/-- info: true -/
#guard_msgs in
#eval pricingShippingThresholdPass

/-- info: true -/
#guard_msgs in
#eval pricingOrderTotalPass

end CommerceTheory.Tests
