import CommerceTheory.Accounting
import CommerceTheory.Catalog

namespace CommerceTheory.Tests

def catalogAccountingSku : Sku :=
  { value := 7001 }

def catalogAccountingBrand : Brand :=
  { id := 1, name := "Brand" }

def catalogAccountingCategory : Category :=
  { id := 2, name := "Category" }

def catalogAccountingProduct : Product :=
  { id := { value := 3 }
    brand := catalogAccountingBrand
    category := catalogAccountingCategory
    status := ProductStatus.Active }

def catalogAccountingVariant : ProductVariant :=
  { id := { value := 4 }
    productId := catalogAccountingProduct.id
    sku := catalogAccountingSku
    active := true }

def catalogAccountingEntry : ProductCatalogEntry :=
  { product := catalogAccountingProduct
    variant := catalogAccountingVariant
    variant_belongs_to_product := rfl }

example : catalogEntry_variant_belongs_to_product catalogAccountingEntry = rfl := by
  rfl

def catalogAccountingAccount (id : Id) (name : String) : LedgerAccount :=
  { id := id, name := name }

def catalogAccountingAccounts : AccountingAccounts :=
  { cash := catalogAccountingAccount 1 "Cash"
    deferredRevenue := catalogAccountingAccount 2 "Deferred revenue"
    revenue := catalogAccountingAccount 3 "Revenue"
    refunds := catalogAccountingAccount 4 "Refunds"
    inventory := catalogAccountingAccount 5 "Inventory"
    cogs := catalogAccountingAccount 6 "COGS" }

def catalogAccountingExamplesPass : Bool :=
  debitTotal (paymentCapturedJournal catalogAccountingAccounts 4200).postings == 4200 &&
    creditTotal (paymentCapturedJournal catalogAccountingAccounts 4200).postings == 4200 &&
    debitTotal (refundIssuedJournal catalogAccountingAccounts 900).postings == 900 &&
    creditTotal (refundIssuedJournal catalogAccountingAccounts 900).postings == 900

/-- info: true -/
#guard_msgs in
#eval catalogAccountingExamplesPass

end CommerceTheory.Tests
