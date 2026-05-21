import CommerceTheory.CompetitorPricing
import CommerceTheory.Merchandising

namespace CommerceTheory.Tests

def competitorMerchandisingSku : Sku :=
  { value := 7301 }

def competitorMerchandisingCosts : DropshipProfitCosts :=
  { supplierGoods := 500
    supplierShipping := 100
    marketplaceFee := 80
    paymentFee := 30
    adSpend := 120
    returnReserve := 40
    tax := 20
    otherCosts := 10 }

def competitorExamplesPass : Bool :=
  customerNetAtOfferPrice 1500 200 == 1300 &&
    profitablePriceFloor competitorMerchandisingCosts 250 100 == 1250 &&
    undercutPrice 1400 50 == 1350 &&
    targetPriceFromStrategy (CompetitivePricingStrategy.Undercut 50) 1400 == 1350

def merchandisingExamplesPass : Bool :=
  componentRequiredForBundles 4
      { sku := competitorMerchandisingSku
        unitsPerBundle := 2
        stockAvailable := 20
        units_pos := by norm_num } == 8 &&
    targetPriceFromStrategy CompetitivePricingStrategy.Match 1400 == 1400

example :
    advertisedPriceAllowed
      { mapPrice := 900, msrp := 1200, map_le_msrp := by norm_num }
      950 := by
  simp [advertisedPriceAllowed]

example :
    promotionSetAllowedByPolicy
      PromotionStackingPolicy.Stackable
      3
      { resultingPrice := 1000
        totalDiscount := 200
        discountCap := 300
        profitFloor := 700
        discount_le_cap := by norm_num
        floor_le_price := by norm_num } := by
  simp [promotionSetAllowedByPolicy]

/-- info: true -/
#guard_msgs in
#eval competitorExamplesPass

/-- info: true -/
#guard_msgs in
#eval merchandisingExamplesPass

end CommerceTheory.Tests
