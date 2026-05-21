import CommerceTheory.Forecasting
import CommerceTheory.FulfillmentFinance
import CommerceTheory.PostPurchase
import CommerceTheory.RiskPrivacy
import CommerceTheory.Tax

namespace CommerceTheory.Tests

def financeRiskBasisPoints10Percent : BasisPoints :=
  { value := 1000
    value_le_10000 := by norm_num }

def financeRiskExchangeRate : ExchangeRate :=
  { source := Currency.USD
    target := Currency.EUR
    numerator := 9
    denominator := 10
    denominator_pos := by norm_num
    observedAt := unixEpochTimestamp }

def financeRiskTaxRate : TaxRate :=
  { bps := financeRiskBasisPoints10Percent }

def fulfillmentFinanceExamplesPass : Bool :=
  convertMoneyFloor 100 financeRiskExchangeRate == 90 &&
    taxAmountRounded RoundingMode.HalfUp financeRiskTaxRate 999 == 100 &&
    absDiffNat 10 4 == 6 &&
    absDiffNat 4 10 == 6

def riskPrivacyExamplesPass : Bool :=
  let policy : FraudPolicy :=
    { maxCouponUses := 3
      maxOrdersPerHour := 10
      maxZeroTotalItems := 1 }
  policy.maxCouponUses == 3 &&
    policy.maxOrdersPerHour == 10 &&
    policy.maxZeroTotalItems == 1

example :
    couponUsesAllowed
      { maxCouponUses := 3, maxOrdersPerHour := 10, maxZeroTotalItems := 1 }
      2 := by
  simp [couponUsesAllowed]

example :
    ordersPerHourAllowed
      { maxCouponUses := 3, maxOrdersPerHour := 10, maxZeroTotalItems := 1 }
      10 := by
  simp [ordersPerHourAllowed]

example : CanPerform Role.Admin Action.DeleteOrder := by
  exact admin_can_perform Action.DeleteOrder

example : CanPerform Role.Warehouse Action.AdjustStock := by
  exact warehouse_can_adjust_stock

example : ¬ CanPerform Role.Customer Action.IssueRefund := by
  exact customer_cannot_issue_refund

def postPurchaseExamplesPass : Bool :=
  let redemption : GiftCardRedemption :=
    { card := { balance := 5000, expiresAt := unixEpochTimestamp }
      amount := 1200
      amount_le_balance := by norm_num }
  giftCardBalanceAfterRedeem redemption == 3800 &&
    cashflowInflowsTotal [{ inflow := 500, outflow := 0 }, { inflow := 125, outflow := 25 }] == 625 &&
    cashflowOutflowsTotal [{ inflow := 500, outflow := 0 }, { inflow := 125, outflow := 25 }] == 25

example : confidenceAllowsAutoReplenish Confidence.Medium := by
  exact mediumConfidence_allows_autoReplenish

example : confidenceAllowsAutoReplenish Confidence.High := by
  exact highConfidence_allows_autoReplenish

example : ¬ confidenceAllowsAutoReplenish Confidence.Low := by
  exact lowConfidence_not_autoReplenish

def taxExamplesPass : Bool :=
  taxForTreatment TaxTreatment.Taxable RoundingMode.HalfUp financeRiskTaxRate 999 == 100 &&
    taxForTreatment TaxTreatment.Exempt RoundingMode.HalfUp financeRiskTaxRate 999 == 0 &&
    sellerTaxDueForFacilitator true 250 == 0 &&
    sellerTaxDueForFacilitator false 250 == 250

/-- info: true -/
#guard_msgs in
#eval fulfillmentFinanceExamplesPass

/-- info: true -/
#guard_msgs in
#eval riskPrivacyExamplesPass

/-- info: true -/
#guard_msgs in
#eval postPurchaseExamplesPass

/-- info: true -/
#guard_msgs in
#eval taxExamplesPass

end CommerceTheory.Tests
