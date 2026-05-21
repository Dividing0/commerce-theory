import CommerceTheory.B2B
import CommerceTheory.DropshipProfit
import CommerceTheory.Dropshipping

namespace CommerceTheory.Tests

def b2bDropshipSku : Sku :=
  { value := 7201 }

def b2bTradeEntry : TradePriceBookEntry :=
  { sku := b2bDropshipSku
    currency := Currency.USD
    unitCost := 600
    retailUnitPrice := 1200
    wholesaleUnitPrice := 900
    retailMargin := 300
    wholesaleMargin := 100
    wholesaleMinQty := 3
    retail_margin_ok := by norm_num
    wholesale_margin_ok := by norm_num
    wholesalePrice_le_retailPrice := by norm_num
    wholesaleMinQty_pos := by norm_num }

def b2bWholesaleLine : WholesaleLine :=
  { entry := b2bTradeEntry
    quantity := 4
    minQty_ok := by
      change 3 ≤ 4
      norm_num
    discount := 200
    discount_le_gross := by
      change 200 ≤ 900 * 4
      norm_num }

def b2bExamplesPass : Bool :=
  unitPriceForTradeMode TradeMode.Retail b2bTradeEntry == 1200 &&
    unitPriceForTradeMode TradeMode.Wholesale b2bTradeEntry == 900 &&
    wholesaleLineGrossTotal b2bWholesaleLine == 3600 &&
    wholesaleLineNetTotal b2bWholesaleLine == 3400 &&
    wholesaleOrderNetTotal [b2bWholesaleLine] == 3400

def dropshipSupplierExample : DropshipSupplier :=
  { id := { value := 10 }
    name := "Supplier"
    currency := Currency.USD
    active := true
    suspended := false
    processingDays := days 3
    acceptsReturns := true
    maxDailyOrders := 50 }

def dropshipProfitCostsExample : DropshipProfitCosts :=
  { supplierGoods := 500
    supplierShipping := 100
    marketplaceFee := 80
    paymentFee := 30
    adSpend := 120
    returnReserve := 40
    tax := 20
    otherCosts := 10 }

def dropshipProfitExamplesPass : Bool :=
  dropshipProfitCostsTotal dropshipProfitCostsExample == 900 &&
    requiredRevenueForProfit (dropshipProfitCostsTotal dropshipProfitCostsExample) 250 == 1150 &&
    requiredGrossForProfit (dropshipProfitCostsTotal dropshipProfitCostsExample) 250 100 == 1250 &&
    profitAfterAdSpend 2000 900 100 == 1000

example : supplierCanReceiveOrders dropshipSupplierExample := by
  simp [supplierCanReceiveOrders, dropshipSupplierExample]

/-- info: true -/
#guard_msgs in
#eval b2bExamplesPass

/-- info: true -/
#guard_msgs in
#eval dropshipProfitExamplesPass

end CommerceTheory.Tests
