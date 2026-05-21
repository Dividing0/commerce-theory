import CommerceTheory.Orders

namespace CommerceTheory

/-! ## 5. Accounting, double-entry ledger, and event projections -/

/-!
Accounting is modeled with a small double-entry ledger. A `BalancedJournalEntry`
contains the postings and a proof that total debits equal total credits.
-/

/-- Closed set of cases for `PostingSide` in the commerce domain model. -/
inductive PostingSide where
  | Debit
  | Credit
deriving DecidableEq, Repr

/-- Data shape for `LedgerAccount`; proof fields record invariants when needed. -/
structure LedgerAccount where
  id : Id
  name : String

/-- Data shape for `Posting`; proof fields record invariants when needed. -/
structure Posting where
  account : LedgerAccount
  side : PostingSide
  amount : Money

/-- Computes or checks `debit` using the validated data in this module. -/
def debit (account : LedgerAccount) (amount : Money) : Posting :=
  { account := account, side := PostingSide.Debit, amount := amount }

/-- Computes or checks `credit` using the validated data in this module. -/
def credit (account : LedgerAccount) (amount : Money) : Posting :=
  { account := account, side := PostingSide.Credit, amount := amount }

/-- Computes or checks `debitTotal` using the validated data in this module. -/
def debitTotal : List Posting → Money
  | [] => 0
  | p :: rest => (if p.side = PostingSide.Debit then p.amount else 0) + debitTotal rest

/-- Computes or checks `creditTotal` using the validated data in this module. -/
def creditTotal : List Posting → Money
  | [] => 0
  | p :: rest => (if p.side = PostingSide.Credit then p.amount else 0) + creditTotal rest

/-- Data shape for `BalancedJournalEntry`; proof fields record invariants when needed. -/
structure BalancedJournalEntry where
  postings : List Posting
  balanced : debitTotal postings = creditTotal postings

/-- Any balanced journal entry exposes equality of debit and credit totals. -/
theorem balancedJournalEntry_balanced (entry : BalancedJournalEntry) :
    debitTotal entry.postings = creditTotal entry.postings := by
  exact entry.balanced

/-- Data shape for `AccountingAccounts`; proof fields record invariants when needed. -/
structure AccountingAccounts where
  cash : LedgerAccount
  deferredRevenue : LedgerAccount
  revenue : LedgerAccount
  refunds : LedgerAccount
  inventory : LedgerAccount
  cogs : LedgerAccount

/-- Computes or checks `paymentCapturedJournal` using the validated data in this module. -/
def paymentCapturedJournal (accounts : AccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings := [debit accounts.cash amount, credit accounts.deferredRevenue amount]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Computes or checks `refundIssuedJournal` using the validated data in this module. -/
def refundIssuedJournal (accounts : AccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings := [debit accounts.refunds amount, credit accounts.cash amount]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- States the safety property captured by `paymentCapturedJournal_balanced`. -/
theorem paymentCapturedJournal_balanced (accounts : AccountingAccounts) (amount : Money) :
    debitTotal (paymentCapturedJournal accounts amount).postings =
      creditTotal (paymentCapturedJournal accounts amount).postings := by
  exact (paymentCapturedJournal accounts amount).balanced

/-- Refund-issued journal entries are balanced by construction. -/
theorem refundIssuedJournal_balanced (accounts : AccountingAccounts) (amount : Money) :
    debitTotal (refundIssuedJournal accounts amount).postings =
      creditTotal (refundIssuedJournal accounts amount).postings := by
  exact (refundIssuedJournal accounts amount).balanced

/-- Capturing payment debits cash for exactly the captured amount. -/
theorem paymentCapturedJournal_debitTotal
    (accounts : AccountingAccounts) (amount : Money) :
    debitTotal (paymentCapturedJournal accounts amount).postings = amount := by
  simp [paymentCapturedJournal, debitTotal, debit, credit]

/-- Capturing payment credits deferred revenue for exactly the captured amount. -/
theorem paymentCapturedJournal_creditTotal
    (accounts : AccountingAccounts) (amount : Money) :
    creditTotal (paymentCapturedJournal accounts amount).postings = amount := by
  simp [paymentCapturedJournal, creditTotal, debit, credit]

/-- Issuing a refund debits refunds expense for exactly the refunded amount. -/
theorem refundIssuedJournal_debitTotal
    (accounts : AccountingAccounts) (amount : Money) :
    debitTotal (refundIssuedJournal accounts amount).postings = amount := by
  simp [refundIssuedJournal, debitTotal, debit, credit]

/-- Issuing a refund credits cash for exactly the refunded amount. -/
theorem refundIssuedJournal_creditTotal
    (accounts : AccountingAccounts) (amount : Money) :
    creditTotal (refundIssuedJournal accounts amount).postings = amount := by
  simp [refundIssuedJournal, creditTotal, debit, credit]

/-! ### More realistic accounting flows -/

/--
Additional ledger accounts used by accrual accounting, marketplace settlement,
chargeback reserves, tax liabilities, and FX revaluation.
-/
structure AdvancedAccountingAccounts where
  operating : AccountingAccounts
  accountsReceivable : LedgerAccount
  accountsPayable : LedgerAccount
  taxLiability : LedgerAccount
  marketplaceClearing : LedgerAccount
  marketplaceFees : LedgerAccount
  chargebackReserve : LedgerAccount
  chargebackExpense : LedgerAccount
  realizedFxGain : LedgerAccount
  realizedFxLoss : LedgerAccount
  unrealizedFxGain : LedgerAccount
  unrealizedFxLoss : LedgerAccount

/-- Accrual sale: recognize receivable, revenue, and tax liability. -/
def invoiceAccrualJournal
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) : BalancedJournalEntry :=
  { postings :=
      [ debit accounts.accountsReceivable total
      , credit accounts.operating.revenue subtotal
      , credit accounts.taxLiability tax
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit, hTotal] }

/-- Cash sale: cash is received immediately while tax liability remains separate. -/
def cashSaleJournal
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) : BalancedJournalEntry :=
  { postings :=
      [ debit accounts.operating.cash total
      , credit accounts.operating.revenue subtotal
      , credit accounts.taxLiability tax
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit, hTotal] }

/-- Later cash collection against a previously accrued receivable. -/
def receivableCollectionJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.operating.cash amount
      , credit accounts.accountsReceivable amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Supplier bill accrual: inventory/expense is recognized against accounts payable. -/
def supplierBillJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.operating.inventory amount
      , credit accounts.accountsPayable amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Supplier payment clears accounts payable with cash. -/
def supplierPaymentJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.accountsPayable amount
      , credit accounts.operating.cash amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Marketplace sale recognized into a marketplace clearing account. -/
def marketplaceSaleClearingJournal
    (accounts : AdvancedAccountingAccounts) (gross : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.marketplaceClearing gross
      , credit accounts.operating.revenue gross
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Marketplace settlement clears gross sales into payout cash and marketplace fees. -/
def marketplaceSettlementJournal
    (accounts : AdvancedAccountingAccounts)
    (gross fee payout : Money)
    (hSettlement : payout + fee = gross) : BalancedJournalEntry :=
  { postings :=
      [ debit accounts.operating.cash payout
      , debit accounts.marketplaceFees fee
      , credit accounts.marketplaceClearing gross
      ]
    balanced := by
      simpa [debitTotal, creditTotal, debit, credit, Nat.add_assoc] using hSettlement }

/--
Full marketplace payout reconciliation across gross sales, fees, refunds,
reserves, facilitator taxes, and payout cash.
-/
def marketplacePayoutReconciliationJournal
    (accounts : AdvancedAccountingAccounts)
    (gross fee refund reserve tax payout : Money)
    (hReconciles : payout + fee + refund + reserve + tax = gross) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.operating.cash payout
      , debit accounts.marketplaceFees fee
      , debit accounts.operating.refunds refund
      , debit accounts.chargebackReserve reserve
      , debit accounts.taxLiability tax
      , credit accounts.marketplaceClearing gross
      ]
    balanced := by
      simpa [debitTotal, creditTotal, debit, credit, Nat.add_assoc] using hReconciles }

/-- Chargeback reserve accrual separates expected chargebacks from cash movement. -/
def chargebackReserveJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.chargebackExpense amount
      , credit accounts.chargebackReserve amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Chargeback settlement releases reserve against cash. -/
def chargebackSettlementJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.chargebackReserve amount
      , credit accounts.operating.cash amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Unrealized FX gain on an open receivable. -/
def unrealizedFxGainJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.accountsReceivable amount
      , credit accounts.unrealizedFxGain amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Unrealized FX loss on an open receivable. -/
def unrealizedFxLossJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.unrealizedFxLoss amount
      , credit accounts.accountsReceivable amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Realized FX gain when cash settlement exceeds the recorded functional value. -/
def realizedFxGainJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.operating.cash amount
      , credit accounts.realizedFxGain amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Realized FX loss when cash settlement is below the recorded functional value. -/
def realizedFxLossJournal
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    BalancedJournalEntry :=
  { postings :=
      [ debit accounts.realizedFxLoss amount
      , credit accounts.operating.cash amount
      ]
    balanced := by
      simp [debitTotal, creditTotal, debit, credit] }

/-- Accrual invoices remain balanced. -/
theorem invoiceAccrualJournal_balanced
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    debitTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings =
      creditTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings := by
  exact (invoiceAccrualJournal accounts subtotal tax total hTotal).balanced

/-- Cash-sale journals remain balanced. -/
theorem cashSaleJournal_balanced
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    debitTotal (cashSaleJournal accounts subtotal tax total hTotal).postings =
      creditTotal (cashSaleJournal accounts subtotal tax total hTotal).postings := by
  exact (cashSaleJournal accounts subtotal tax total hTotal).balanced

/-- Accrual invoice debit total is the full invoice total. -/
theorem invoiceAccrualJournal_debitTotal
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    debitTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings = total := by
  simp [invoiceAccrualJournal, debitTotal, debit, credit]

/-- Accrual invoice credit total recovers revenue plus tax liability. -/
theorem invoiceAccrualJournal_creditTotal
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    creditTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings =
      subtotal + tax := by
  simp [invoiceAccrualJournal, creditTotal, debit, credit]

/-- The tax component is included in the credit side of an accrual invoice. -/
theorem invoiceAccrualJournal_tax_le_creditTotal
    (accounts : AdvancedAccountingAccounts)
    (subtotal tax total : Money)
    (hTotal : total = subtotal + tax) :
    tax ≤ creditTotal (invoiceAccrualJournal accounts subtotal tax total hTotal).postings := by
  rw [invoiceAccrualJournal_creditTotal accounts subtotal tax total hTotal]
  exact Nat.le_add_left tax subtotal

/-- Receivable collections remain balanced. -/
theorem receivableCollectionJournal_balanced
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (receivableCollectionJournal accounts amount).postings =
      creditTotal (receivableCollectionJournal accounts amount).postings := by
  exact (receivableCollectionJournal accounts amount).balanced

/-- Supplier bills remain balanced. -/
theorem supplierBillJournal_balanced
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (supplierBillJournal accounts amount).postings =
      creditTotal (supplierBillJournal accounts amount).postings := by
  exact (supplierBillJournal accounts amount).balanced

/-- Supplier payments remain balanced. -/
theorem supplierPaymentJournal_balanced
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (supplierPaymentJournal accounts amount).postings =
      creditTotal (supplierPaymentJournal accounts amount).postings := by
  exact (supplierPaymentJournal accounts amount).balanced

/-- Marketplace clearing sale entries remain balanced. -/
theorem marketplaceSaleClearingJournal_balanced
    (accounts : AdvancedAccountingAccounts) (gross : Money) :
    debitTotal (marketplaceSaleClearingJournal accounts gross).postings =
      creditTotal (marketplaceSaleClearingJournal accounts gross).postings := by
  exact (marketplaceSaleClearingJournal accounts gross).balanced

/-- Marketplace settlement journals remain balanced when payout plus fee recovers gross. -/
theorem marketplaceSettlementJournal_balanced
    (accounts : AdvancedAccountingAccounts)
    (gross fee payout : Money)
    (hSettlement : payout + fee = gross) :
    debitTotal (marketplaceSettlementJournal accounts gross fee payout hSettlement).postings =
      creditTotal (marketplaceSettlementJournal accounts gross fee payout hSettlement).postings := by
  exact (marketplaceSettlementJournal accounts gross fee payout hSettlement).balanced

/-- Marketplace settlement debit total recovers gross. -/
theorem marketplaceSettlementJournal_debitTotal_eq_gross
    (accounts : AdvancedAccountingAccounts)
    (gross fee payout : Money)
    (hSettlement : payout + fee = gross) :
    debitTotal (marketplaceSettlementJournal accounts gross fee payout hSettlement).postings =
      gross := by
  simpa [marketplaceSettlementJournal, debitTotal, debit, credit, Nat.add_assoc]
    using hSettlement

/-- Full marketplace payout reconciliation remains balanced. -/
theorem marketplacePayoutReconciliationJournal_balanced
    (accounts : AdvancedAccountingAccounts)
    (gross fee refund reserve tax payout : Money)
    (hReconciles : payout + fee + refund + reserve + tax = gross) :
    debitTotal
        (marketplacePayoutReconciliationJournal
          accounts gross fee refund reserve tax payout hReconciles).postings =
      creditTotal
        (marketplacePayoutReconciliationJournal
          accounts gross fee refund reserve tax payout hReconciles).postings := by
  exact
    (marketplacePayoutReconciliationJournal
      accounts gross fee refund reserve tax payout hReconciles).balanced

/-- Full marketplace payout reconciliation conserves the gross clearing balance. -/
theorem marketplacePayoutReconciliationJournal_debitTotal_eq_gross
    (accounts : AdvancedAccountingAccounts)
    (gross fee refund reserve tax payout : Money)
    (hReconciles : payout + fee + refund + reserve + tax = gross) :
    debitTotal
        (marketplacePayoutReconciliationJournal
          accounts gross fee refund reserve tax payout hReconciles).postings =
      gross := by
  simpa [marketplacePayoutReconciliationJournal, debitTotal, debit, credit,
    Nat.add_assoc] using hReconciles

/-- Chargeback reserve accrual journals remain balanced. -/
theorem chargebackReserveJournal_balanced
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (chargebackReserveJournal accounts amount).postings =
      creditTotal (chargebackReserveJournal accounts amount).postings := by
  exact (chargebackReserveJournal accounts amount).balanced

/-- Chargeback settlement journals remain balanced. -/
theorem chargebackSettlementJournal_balanced
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (chargebackSettlementJournal accounts amount).postings =
      creditTotal (chargebackSettlementJournal accounts amount).postings := by
  exact (chargebackSettlementJournal accounts amount).balanced

/-- Realized and unrealized FX gain/loss journals are all balanced. -/
theorem fxRevaluationJournals_balanced
    (accounts : AdvancedAccountingAccounts) (amount : Money) :
    debitTotal (unrealizedFxGainJournal accounts amount).postings =
        creditTotal (unrealizedFxGainJournal accounts amount).postings ∧
      debitTotal (unrealizedFxLossJournal accounts amount).postings =
        creditTotal (unrealizedFxLossJournal accounts amount).postings ∧
      debitTotal (realizedFxGainJournal accounts amount).postings =
        creditTotal (realizedFxGainJournal accounts amount).postings ∧
      debitTotal (realizedFxLossJournal accounts amount).postings =
        creditTotal (realizedFxLossJournal accounts amount).postings := by
  exact ⟨(unrealizedFxGainJournal accounts amount).balanced,
    (unrealizedFxLossJournal accounts amount).balanced,
    (realizedFxGainJournal accounts amount).balanced,
    (realizedFxLossJournal accounts amount).balanced⟩

end CommerceTheory
