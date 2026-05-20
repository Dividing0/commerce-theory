import WebshopTheory.Orders

namespace WebShopTheoryComplete

/-! ## 5. Accounting, double-entry ledger, and event projections -/

/-!
Accounting is modeled with a small double-entry ledger. A `BalancedJournalEntry`
contains the postings and a proof that total debits equal total credits.
-/

/-- Closed set of cases for `PostingSide` in the webshop domain model. -/
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


end WebShopTheoryComplete
