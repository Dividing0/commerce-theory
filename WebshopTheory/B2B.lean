import WebshopTheory.Marketing

namespace WebShopTheoryComplete

/-! ## 8. Retail, wholesale, B2B, and credit terms -/

/-!
B2B logic extends retail pricing with customer kinds, wholesale price books,
minimum order quantities, payment terms, and credit limits. The proofs make sure
wholesale discounts and credit orders remain within declared business limits.
-/

/-- Closed set of cases for `TradeMode` in the webshop domain model. -/
inductive TradeMode where
  | Retail
  | Wholesale
deriving DecidableEq, Repr

/-- Closed set of cases for `CustomerKind` in the webshop domain model. -/
inductive CustomerKind where
  | Guest
  | Registered
  | WholesaleAccount
deriving DecidableEq, Repr

/-- Data shape for `Customer`; proof fields record invariants when needed. -/
structure Customer where
  id : CustomerId
  kind : CustomerKind
  wholesaleApproved : Bool

/-- Computes or checks `customerCanBuyWholesale` using the validated data in this module. -/
def customerCanBuyWholesale (customer : Customer) : Prop :=
  customer.kind = CustomerKind.WholesaleAccount ∧ customer.wholesaleApproved = true

/-- States the safety property captured by `wholesaleCustomer_has_wholesale_kind`. -/
theorem wholesaleCustomer_has_wholesale_kind (customer : Customer)
    (h : customerCanBuyWholesale customer) :
    customer.kind = CustomerKind.WholesaleAccount := by
  exact h.left

/-- Closed set of cases for `PaymentTerms` in the webshop domain model. -/
inductive PaymentTerms where
  | Prepaid
  | NetDays : Nat → PaymentTerms
deriving DecidableEq, Repr

/-- Computes or checks `paymentTermsAllowed` using the validated data in this module. -/
def paymentTermsAllowed : TradeMode → PaymentTerms → Prop
  | TradeMode.Retail, PaymentTerms.Prepaid => True
  | TradeMode.Retail, PaymentTerms.NetDays _ => False
  | TradeMode.Wholesale, _ => True

/-- States the safety property captured by `retail_net_terms_not_allowed`. -/
theorem retail_net_terms_not_allowed (days : Nat) :
    ¬ paymentTermsAllowed TradeMode.Retail (PaymentTerms.NetDays days) := by
  simp [paymentTermsAllowed]

/-- States the safety property captured by `retail_terms_allowed_implies_prepaid`. -/
theorem retail_terms_allowed_implies_prepaid
    (terms : PaymentTerms) (h : paymentTermsAllowed TradeMode.Retail terms) :
    terms = PaymentTerms.Prepaid := by
  cases terms with
  | Prepaid => rfl
  | NetDays days => simp [paymentTermsAllowed] at h

/-- Data shape for `TradePriceBookEntry`; proof fields record invariants when needed. -/
structure TradePriceBookEntry where
  sku : Sku
  currency : Currency
  unitCost : Money
  retailUnitPrice : Money
  wholesaleUnitPrice : Money
  retailMargin : Money
  wholesaleMargin : Money
  wholesaleMinQty : Quantity
  retail_margin_ok : unitCost + retailMargin ≤ retailUnitPrice
  wholesale_margin_ok : unitCost + wholesaleMargin ≤ wholesaleUnitPrice
  wholesalePrice_le_retailPrice : wholesaleUnitPrice ≤ retailUnitPrice
  wholesaleMinQty_pos : 0 < wholesaleMinQty

/-- Computes or checks `unitPriceForTradeMode` using the validated data in this module. -/
def unitPriceForTradeMode (mode : TradeMode) (entry : TradePriceBookEntry) : Money :=
  match mode with
  | TradeMode.Retail => entry.retailUnitPrice
  | TradeMode.Wholesale => entry.wholesaleUnitPrice

/-- States the safety property captured by `tradeEntry_wholesale_cost_le_price`. -/
theorem tradeEntry_wholesale_cost_le_price (entry : TradePriceBookEntry) :
    entry.unitCost ≤ entry.wholesaleUnitPrice := by
  exact Nat.le_of_add_right_le entry.wholesale_margin_ok

/-- States the safety property captured by `wholesaleUnitPrice_le_retailUnitPrice`. -/
theorem wholesaleUnitPrice_le_retailUnitPrice (entry : TradePriceBookEntry) :
    entry.wholesaleUnitPrice ≤ entry.retailUnitPrice := by
  exact entry.wholesalePrice_le_retailPrice

/-- Data shape for `RetailLine`; proof fields record invariants when needed. -/
structure RetailLine where
  entry : TradePriceBookEntry
  quantity : Quantity
  discount : Money
  discount_le_gross : discount ≤ entry.retailUnitPrice * quantity

/-- Computes or checks `retailLineGrossTotal` using the validated data in this module. -/
def retailLineGrossTotal (line : RetailLine) : Money :=
  line.entry.retailUnitPrice * line.quantity

/-- Computes or checks `retailLineNetTotal` using the validated data in this module. -/
def retailLineNetTotal (line : RetailLine) : Money :=
  retailLineGrossTotal line - line.discount

/-- States the safety property captured by `retailLineNet_le_grossTotal`. -/
theorem retailLineNet_le_grossTotal (line : RetailLine) :
    retailLineNetTotal line ≤ retailLineGrossTotal line := by
  unfold retailLineNetTotal
  exact Nat.sub_le (retailLineGrossTotal line) line.discount

/-- Data shape for `WholesaleLine`; proof fields record invariants when needed. -/
structure WholesaleLine where
  entry : TradePriceBookEntry
  quantity : Quantity
  minQty_ok : entry.wholesaleMinQty ≤ quantity
  discount : Money
  discount_le_gross : discount ≤ entry.wholesaleUnitPrice * quantity

/-- Computes or checks `wholesaleLineGrossTotal` using the validated data in this module. -/
def wholesaleLineGrossTotal (line : WholesaleLine) : Money :=
  line.entry.wholesaleUnitPrice * line.quantity

/-- Computes or checks `wholesaleLineRetailEquivalentTotal` using the validated data in this module. -/
def wholesaleLineRetailEquivalentTotal (line : WholesaleLine) : Money :=
  line.entry.retailUnitPrice * line.quantity

/-- Computes or checks `wholesaleLineNetTotal` using the validated data in this module. -/
def wholesaleLineNetTotal (line : WholesaleLine) : Money :=
  wholesaleLineGrossTotal line - line.discount

/-- States the safety property captured by `wholesaleLine_meets_minimum_quantity`. -/
theorem wholesaleLine_meets_minimum_quantity (line : WholesaleLine) :
    line.entry.wholesaleMinQty ≤ line.quantity := by
  exact line.minQty_ok

/-- States the safety property captured by `wholesaleLineGross_le_retailEquivalent`. -/
theorem wholesaleLineGross_le_retailEquivalent (line : WholesaleLine) :
    wholesaleLineGrossTotal line ≤ wholesaleLineRetailEquivalentTotal line := by
  unfold wholesaleLineGrossTotal
  unfold wholesaleLineRetailEquivalentTotal
  exact Nat.mul_le_mul_right line.quantity line.entry.wholesalePrice_le_retailPrice

/-- Computes or checks `wholesaleOrderNetTotal` using the validated data in this module. -/
def wholesaleOrderNetTotal : List WholesaleLine → Money
  | [] => 0
  | line :: rest => wholesaleLineNetTotal line + wholesaleOrderNetTotal rest

/-- Computes or checks `wholesaleRetailEquivalentTotal` using the validated data in this module. -/
def wholesaleRetailEquivalentTotal : List WholesaleLine → Money
  | [] => 0
  | line :: rest => wholesaleLineRetailEquivalentTotal line + wholesaleRetailEquivalentTotal rest

/-- States the safety property captured by `wholesaleLineNet_le_retailEquivalent`. -/
theorem wholesaleLineNet_le_retailEquivalent (line : WholesaleLine) :
    wholesaleLineNetTotal line ≤ wholesaleLineRetailEquivalentTotal line := by
  have h1 : wholesaleLineNetTotal line ≤ wholesaleLineGrossTotal line := by
    unfold wholesaleLineNetTotal
    exact Nat.sub_le (wholesaleLineGrossTotal line) line.discount
  have h2 := wholesaleLineGross_le_retailEquivalent line
  exact h1.trans h2

/-- States the safety property captured by `wholesaleOrderNetTotal_le_retailEquivalentTotal`. -/
theorem wholesaleOrderNetTotal_le_retailEquivalentTotal (lines : List WholesaleLine) :
    wholesaleOrderNetTotal lines ≤ wholesaleRetailEquivalentTotal lines := by
  induction lines with
  | nil => simp [wholesaleOrderNetTotal, wholesaleRetailEquivalentTotal]
  | cons line rest ih =>
      have hline := wholesaleLineNet_le_retailEquivalent line
      simpa [wholesaleOrderNetTotal, wholesaleRetailEquivalentTotal] using Nat.add_le_add hline ih

/-- Data shape for `WholesaleCreditAccount`; proof fields record invariants when needed. -/
structure WholesaleCreditAccount where
  customer : Customer
  creditLimit : Money
  outstanding : Money
  customer_can_buy_wholesale : customerCanBuyWholesale customer
  outstanding_le_limit : outstanding ≤ creditLimit

/-- Computes or checks `canPlaceWholesaleCreditOrder` using the validated data in this module. -/
def canPlaceWholesaleCreditOrder (account : WholesaleCreditAccount) (orderTotal : Money) : Prop :=
  account.outstanding + orderTotal ≤ account.creditLimit

/-- States the safety property captured by `wholesaleCredit_order_keeps_limit_safe`. -/
theorem wholesaleCredit_order_keeps_limit_safe
    (account : WholesaleCreditAccount) (orderTotal : Money)
    (h : canPlaceWholesaleCreditOrder account orderTotal) :
    account.outstanding + orderTotal ≤ account.creditLimit := by
  exact h


end WebShopTheoryComplete
