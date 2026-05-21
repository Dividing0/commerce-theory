import CommerceTheory.FulfillmentFinance

namespace CommerceTheory

/-! ## 20. Tax, VAT/GST, and invoicing -/

/-!
This module promotes tax from an order-total component into a first-class
compliance domain. It models jurisdictions, taxable/exempt/reverse-charge
treatments, VAT/GST-inclusive pricing, invoice totals, marketplace facilitator
tax, and B2B exemption certificate evidence.
-/

/-- Supported tax regimes for a jurisdiction. -/
inductive TaxRegime where
  | SalesTax
  | VAT
  | GST
  | Custom
deriving DecidableEq, Repr

/-- Tax jurisdiction with its governing regime and reporting currency. -/
structure TaxJurisdiction where
  id : Id
  name : String
  regime : TaxRegime
  currency : Currency

/-- Tax treatment assigned to a line or sale. -/
inductive TaxTreatment where
  | Taxable
  | Exempt
  | ZeroRated
  | ReverseCharge
deriving DecidableEq, Repr

/-- Seller-side tax collection is required only for ordinary taxable treatment. -/
def sellerCollectsTaxForTreatment : TaxTreatment → Prop
  | TaxTreatment.Taxable => True
  | TaxTreatment.Exempt => False
  | TaxTreatment.ZeroRated => False
  | TaxTreatment.ReverseCharge => False

/-- Exempt lines require no seller-collected tax. -/
theorem exempt_treatment_has_no_seller_collection :
    ¬ sellerCollectsTaxForTreatment TaxTreatment.Exempt := by
  simp [sellerCollectsTaxForTreatment]

/-- Zero-rated lines require no seller-collected tax at a positive rate. -/
theorem zeroRated_treatment_has_no_seller_collection :
    ¬ sellerCollectsTaxForTreatment TaxTreatment.ZeroRated := by
  simp [sellerCollectsTaxForTreatment]

/-- Reverse-charge sales move tax accounting away from seller collection. -/
theorem reverseCharge_treatment_has_no_seller_collection :
    ¬ sellerCollectsTaxForTreatment TaxTreatment.ReverseCharge := by
  simp [sellerCollectsTaxForTreatment]

/-- Tax amount for a treatment, applying rounding only when the seller collects tax. -/
def taxForTreatment
    (treatment : TaxTreatment)
    (mode : RoundingMode)
    (rate : TaxRate)
    (taxableAmount : Money) : Money :=
  match treatment with
  | TaxTreatment.Taxable => taxAmountRounded mode rate taxableAmount
  | TaxTreatment.Exempt => 0
  | TaxTreatment.ZeroRated => 0
  | TaxTreatment.ReverseCharge => 0

/-- Exempt treatment computes zero seller-collected tax. -/
theorem exempt_taxForTreatment_zero
    (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) :
    taxForTreatment TaxTreatment.Exempt mode rate taxableAmount = 0 := by
  simp [taxForTreatment]

/-- Zero-rated treatment computes zero seller-collected tax. -/
theorem zeroRated_taxForTreatment_zero
    (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) :
    taxForTreatment TaxTreatment.ZeroRated mode rate taxableAmount = 0 := by
  simp [taxForTreatment]

/-- Reverse-charge treatment computes zero seller-collected tax. -/
theorem reverseCharge_taxForTreatment_zero
    (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) :
    taxForTreatment TaxTreatment.ReverseCharge mode rate taxableAmount = 0 := by
  simp [taxForTreatment]

/-- Pricing mode for tax-inclusive and tax-exclusive invoice displays. -/
inductive TaxPriceMode where
  | Exclusive
  | Inclusive
deriving DecidableEq, Repr

/-- Tax-inclusive price decomposition: gross already includes tax. -/
structure TaxInclusivePrice where
  gross : Money
  net : Money
  tax : Money
  gross_correct : gross = net + tax

/-- Tax-exclusive price decomposition: tax is added to the net amount. -/
structure TaxExclusivePrice where
  net : Money
  tax : Money
  total : Money
  total_correct : total = net + tax

/-- VAT/GST-inclusive prices conserve their net and tax components. -/
theorem taxInclusivePrice_conserves_components (price : TaxInclusivePrice) :
    price.net + price.tax = price.gross := by
  exact price.gross_correct.symm

/-- Tax-exclusive prices conserve their net and tax components. -/
theorem taxExclusivePrice_conserves_components (price : TaxExclusivePrice) :
    price.net + price.tax = price.total := by
  exact price.total_correct.symm

/-- One tax-compliant invoice line. -/
structure TaxInvoiceLine where
  sku : Sku
  quantity : Quantity
  unitPrice : Money
  discount : Money
  treatment : TaxTreatment
  rate : TaxRate
  roundingMode : RoundingMode
  taxableAmount : Money
  tax : Money
  total : Money
  discount_le_gross : discount ≤ unitPrice * quantity
  taxableAmount_correct : taxableAmount = unitPrice * quantity - discount
  tax_correct : tax = taxForTreatment treatment roundingMode rate taxableAmount
  total_correct : total = taxableAmount + tax

/-- Invoice-line totals conserve taxable amount and tax. -/
theorem taxInvoiceLine_total_conserves_components (line : TaxInvoiceLine) :
    line.taxableAmount + line.tax = line.total := by
  exact line.total_correct.symm

/-- Exempt invoice lines collect zero seller-side tax. -/
theorem exemptTaxInvoiceLine_tax_zero
    (line : TaxInvoiceLine) (h : line.treatment = TaxTreatment.Exempt) :
    line.tax = 0 := by
  rw [line.tax_correct, h]
  simp [taxForTreatment]

/-- Reverse-charge invoice lines collect zero seller-side tax. -/
theorem reverseChargeTaxInvoiceLine_tax_zero
    (line : TaxInvoiceLine) (h : line.treatment = TaxTreatment.ReverseCharge) :
    line.tax = 0 := by
  rw [line.tax_correct, h]
  simp [taxForTreatment]

/-- Sum taxable invoice-line amounts. -/
def invoiceLineSubtotalTotal : List TaxInvoiceLine → Money
  | [] => 0
  | line :: rest => line.taxableAmount + invoiceLineSubtotalTotal rest

/-- Sum invoice-line tax amounts. -/
def invoiceLineTaxTotal : List TaxInvoiceLine → Money
  | [] => 0
  | line :: rest => line.tax + invoiceLineTaxTotal rest

/-- Sum invoice-line totals. -/
def invoiceLineGrandTotal : List TaxInvoiceLine → Money
  | [] => 0
  | line :: rest => line.total + invoiceLineGrandTotal rest

/-- Tax invoice with explicit component totals and discount bound. -/
structure TaxInvoice where
  id : Id
  issuedAt : Timestamp
  sellerId : Id
  buyerId : CustomerId
  jurisdiction : TaxJurisdiction
  currency : Currency
  lines : List TaxInvoiceLine
  subtotal : Money
  tax : Money
  shipping : Money
  discount : Money
  total : Money
  subtotal_correct : subtotal = invoiceLineSubtotalTotal lines
  tax_correct : tax = invoiceLineTaxTotal lines
  discount_le_components : discount ≤ subtotal + tax + shipping
  total_correct : total = subtotal + tax + shipping - discount

/-- Invoice subtotal matches the sum of line taxable amounts. -/
theorem taxInvoice_subtotal_matches_lines (invoice : TaxInvoice) :
    invoice.subtotal = invoiceLineSubtotalTotal invoice.lines := by
  exact invoice.subtotal_correct

/-- Invoice tax matches the sum of line tax amounts. -/
theorem taxInvoice_tax_matches_lines (invoice : TaxInvoice) :
    invoice.tax = invoiceLineTaxTotal invoice.lines := by
  exact invoice.tax_correct

/-- Invoice total conserves subtotal, tax, shipping, and discounts. -/
theorem invoice_total_conserves_components (invoice : TaxInvoice) :
    invoice.subtotal + invoice.tax + invoice.shipping - invoice.discount =
      invoice.total := by
  exact invoice.total_correct.symm

/-- With a bounded discount, adding discount back recovers invoice components. -/
theorem invoice_total_add_discount_eq_components (invoice : TaxInvoice) :
    invoice.total + invoice.discount =
      invoice.subtotal + invoice.tax + invoice.shipping := by
  rw [invoice.total_correct]
  exact Nat.sub_add_cancel invoice.discount_le_components

/-- Invoice total never exceeds subtotal plus tax plus shipping. -/
theorem taxInvoice_total_le_components (invoice : TaxInvoice) :
    invoice.total ≤ invoice.subtotal + invoice.tax + invoice.shipping := by
  rw [invoice.total_correct]
  exact Nat.sub_le (invoice.subtotal + invoice.tax + invoice.shipping) invoice.discount

/-- Tax exemption certificate for B2B tax-exempt sales. -/
structure TaxExemptionCertificate where
  customerId : CustomerId
  jurisdictionId : Id
  validFrom : Timestamp
  validUntil : Timestamp
  valid_window : validFrom ≤ validUntil

/-- A certificate is valid at a timestamp within its inclusive validity window. -/
def certificateValidAt (certificate : TaxExemptionCertificate) (now : Timestamp) : Prop :=
  certificate.validFrom ≤ now ∧ now ≤ certificate.validUntil

/-- Certificate validity exposes the not-expired bound. -/
theorem certificateValidAt_not_expired
    (certificate : TaxExemptionCertificate) (now : Timestamp)
    (h : certificateValidAt certificate now) :
    now ≤ certificate.validUntil := by
  exact h.right

/-- B2B tax exemption evidence joins a customer, jurisdiction, and valid certificate. -/
structure B2BTaxExemption where
  customer : Customer
  jurisdiction : TaxJurisdiction
  certificate : TaxExemptionCertificate
  checkedAt : Timestamp
  customer_matches : certificate.customerId = customer.id
  jurisdiction_matches : certificate.jurisdictionId = jurisdiction.id
  wholesale_approved : customer.wholesaleApproved = true
  certificate_valid : certificateValidAt certificate checkedAt

/-- B2B exemption evidence requires an approved wholesale customer. -/
theorem b2bTaxExemption_wholesale_approved (exemption : B2BTaxExemption) :
    exemption.customer.wholesaleApproved = true := by
  exact exemption.wholesale_approved

/-- B2B exemption evidence carries a still-valid certificate. -/
theorem b2bTaxExemption_certificate_not_expired (exemption : B2BTaxExemption) :
    exemption.checkedAt ≤ exemption.certificate.validUntil := by
  exact certificateValidAt_not_expired
    exemption.certificate exemption.checkedAt exemption.certificate_valid

/-- A B2B exemption certificate justifies exempt tax treatment. -/
theorem b2bExemption_collects_zero_tax
    (exemption : B2BTaxExemption)
    (mode : RoundingMode) (rate : TaxRate) (taxableAmount : Money) :
    exemption.customer.wholesaleApproved = true ∧
      taxForTreatment TaxTreatment.Exempt mode rate taxableAmount = 0 := by
  exact ⟨exemption.wholesale_approved,
    exempt_taxForTreatment_zero mode rate taxableAmount⟩

/-- Seller tax due when a marketplace facilitator may collect tax. -/
def sellerTaxDueForFacilitator (facilitatorCollects : Bool) (tax : Money) : Money :=
  if facilitatorCollects then 0 else tax

/-- Marketplace-facilitator tax collection evidence. -/
structure MarketplaceFacilitatorTax where
  marketplace : Marketplace
  jurisdiction : TaxJurisdiction
  taxableAmount : Money
  rate : TaxRate
  roundingMode : RoundingMode
  tax : Money
  facilitatorCollects : Bool
  sellerTaxDue : Money
  tax_correct : tax = taxAmountRounded roundingMode rate taxableAmount
  sellerTaxDue_correct : sellerTaxDue = sellerTaxDueForFacilitator facilitatorCollects tax

/-- Facilitator tax calculations expose the declared rounding mode. -/
theorem marketplaceFacilitatorTax_uses_declared_rounding
    (tax : MarketplaceFacilitatorTax) :
    tax.tax = taxAmountRounded tax.roundingMode tax.rate tax.taxableAmount := by
  exact tax.tax_correct

/-- When the marketplace facilitator collects tax, seller tax due is zero. -/
theorem marketplaceFacilitator_collected_zero_seller_due
    (tax : MarketplaceFacilitatorTax)
    (hCollects : tax.facilitatorCollects = true) :
    tax.sellerTaxDue = 0 := by
  rw [tax.sellerTaxDue_correct, hCollects]
  simp [sellerTaxDueForFacilitator]

/-- Invoice-line floor tax rounding error is bounded by one minor unit. -/
theorem invoiceLine_floor_tax_rounding_error_lt_one_minor_unit
    (line : TaxInvoiceLine) :
    floorRoundingRemainder
        (line.taxableAmount * line.rate.bps.value) 10000 < 10000 := by
  exact tax_floor_rounding_error_lt_one_minor_unit line.rate line.taxableAmount

/-- Invoice-line floor tax rounding error is bounded by one minor unit per line. -/
theorem invoiceLines_floor_tax_rounding_error_le_one_minor_unit_per_line
    (lines : List TaxInvoiceLine) :
    floorRoundedLinesRemainderTotal 10000
        (lines.map (fun line => line.taxableAmount * line.rate.bps.value)) ≤
      lines.length * 10000 := by
  simpa using
    floorRoundedLinesRemainderTotal_le_one_minor_unit_per_line
      10000
      (lines.map (fun line => line.taxableAmount * line.rate.bps.value))
      (by norm_num)

end CommerceTheory
