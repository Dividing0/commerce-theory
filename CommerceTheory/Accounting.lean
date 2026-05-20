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


end CommerceTheory
