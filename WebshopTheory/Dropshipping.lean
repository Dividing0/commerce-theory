import WebshopTheory.B2B

namespace WebShopTheoryComplete

/-! ## 9. Dropshipping suppliers, offers, reservations, PO, SLA, returns -/

/-!
Dropshipping introduces supplier-side stock, reservations, purchase orders, SLA
checks, and returns. The core invariant is that supplier cost and refund amounts
cannot exceed the customer-facing amounts they relate to.
-/

/-- Data shape for `DropshipSupplier`; proof fields record invariants when needed. -/
structure DropshipSupplier where
  id : SupplierId
  name : String
  currency : Currency
  active : Bool
  suspended : Bool
  processingDays : Days
  acceptsReturns : Bool
  maxDailyOrders : Nat

/-- Computes or checks `supplierCanReceiveOrders` using the validated data in this module. -/
def supplierCanReceiveOrders (supplier : DropshipSupplier) : Prop :=
  supplier.active = true ∧ supplier.suspended = false

/-- States the safety property captured by `supplierCanReceiveOrders_implies_active`. -/
theorem supplierCanReceiveOrders_implies_active
    (supplier : DropshipSupplier) (h : supplierCanReceiveOrders supplier) :
    supplier.active = true := by
  exact h.left

/-- Data shape for `SupplierDailyCapacity`; proof fields record invariants when needed. -/
structure SupplierDailyCapacity where
  supplier : DropshipSupplier
  dailyOrderCapacity : Nat
  ordersAcceptedToday : Nat
  accepted_le_capacity : ordersAcceptedToday ≤ dailyOrderCapacity

/-- Computes or checks `canAddSupplierOrders` using the validated data in this module. -/
def canAddSupplierOrders (capacity : SupplierDailyCapacity) (newOrders : Nat) : Prop :=
  capacity.ordersAcceptedToday + newOrders ≤ capacity.dailyOrderCapacity

/-- Data shape for `DropshipOffer`; proof fields record invariants when needed. -/
structure DropshipOffer where
  sku : Sku
  supplier : DropshipSupplier
  supplierUnitCost : Money
  saleUnitPrice : Money
  unitWeight : Weight
  availableQty : Quantity
  currency : Currency
  active : Bool
  supplierCost_le_salePrice : supplierUnitCost ≤ saleUnitPrice
  currency_matches_supplier : currency = supplier.currency

/-- Computes or checks `dropshipOfferCanBeSold` using the validated data in this module. -/
def dropshipOfferCanBeSold (offer : DropshipOffer) : Prop :=
  supplierCanReceiveOrders offer.supplier ∧ offer.active = true ∧ 0 < offer.availableQty

/-- States the safety property captured by `dropshipOfferCanBeSold_implies_in_stock`. -/
theorem dropshipOfferCanBeSold_implies_in_stock
    (offer : DropshipOffer) (h : dropshipOfferCanBeSold offer) :
    0 < offer.availableQty := by
  exact h.right.right

/-- Closed set of cases for `SupplierReservationStatus` in the webshop domain model. -/
inductive SupplierReservationStatus where
  | Requested
  | Confirmed
  | Rejected
  | Expired
deriving DecidableEq, Repr

/-- Data shape for `SupplierReservation`; proof fields record invariants when needed. -/
structure SupplierReservation where
  offer : DropshipOffer
  supplier : DropshipSupplier
  quantity : Quantity
  status : SupplierReservationStatus
  same_supplier : offer.supplier.id = supplier.id
  quantity_le_available : quantity ≤ offer.availableQty

/-- Computes or checks `reservationConfirmed` using the validated data in this module. -/
def reservationConfirmed (r : SupplierReservation) : Prop :=
  r.status = SupplierReservationStatus.Confirmed

/-- Data shape for `DropshipLine`; proof fields record invariants when needed. -/
structure DropshipLine where
  offer : DropshipOffer
  quantity : Quantity
  discount : Money
  supplier_can_receive_orders : supplierCanReceiveOrders offer.supplier
  offer_active : offer.active = true
  quantity_le_supplier_available : quantity ≤ offer.availableQty
  discount_le_saleGross : discount ≤ offer.saleUnitPrice * quantity
  margin_after_discount_ok : offer.supplierUnitCost * quantity + discount ≤ offer.saleUnitPrice * quantity

/-- Computes or checks `dropshipLineSaleGross` using the validated data in this module. -/
def dropshipLineSaleGross (line : DropshipLine) : Money :=
  line.offer.saleUnitPrice * line.quantity

/-- Computes or checks `dropshipLineCustomerNet` using the validated data in this module. -/
def dropshipLineCustomerNet (line : DropshipLine) : Money :=
  dropshipLineSaleGross line - line.discount

/-- Computes or checks `dropshipLineSupplierCost` using the validated data in this module. -/
def dropshipLineSupplierCost (line : DropshipLine) : Money :=
  line.offer.supplierUnitCost * line.quantity

/-- Computes or checks `dropshipLineWeight` using the validated data in this module. -/
def dropshipLineWeight (line : DropshipLine) : Weight :=
  line.offer.unitWeight * line.quantity

/-- States the safety property captured by `dropshipLineCustomerNet_le_gross`. -/
theorem dropshipLineCustomerNet_le_gross (line : DropshipLine) :
    dropshipLineCustomerNet line ≤ dropshipLineSaleGross line := by
  unfold dropshipLineCustomerNet
  exact Nat.sub_le (dropshipLineSaleGross line) line.discount

/-- States the safety property captured by `dropshipLineSupplierCost_le_customerNet`. -/
theorem dropshipLineSupplierCost_le_customerNet (line : DropshipLine) :
    dropshipLineSupplierCost line ≤ dropshipLineCustomerNet line := by
  unfold dropshipLineSupplierCost
  unfold dropshipLineCustomerNet
  unfold dropshipLineSaleGross
  exact Nat.le_sub_of_add_le line.margin_after_discount_ok

/-- Data shape for `ReservedDropshipLine`; proof fields record invariants when needed. -/
structure ReservedDropshipLine where
  line : DropshipLine
  reservation : SupplierReservation
  same_offer : reservation.offer = line.offer
  same_quantity : reservation.quantity = line.quantity
  confirmed : reservation.status = SupplierReservationStatus.Confirmed

/-- States the safety property captured by `reservedDropshipLine_has_confirmed_reservation`. -/
theorem reservedDropshipLine_has_confirmed_reservation (r : ReservedDropshipLine) :
    reservationConfirmed r.reservation := by
  unfold reservationConfirmed
  exact r.confirmed

/-- Computes or checks `dropshipSaleNetTotal` using the validated data in this module. -/
def dropshipSaleNetTotal : List DropshipLine → Money
  | [] => 0
  | line :: rest => dropshipLineCustomerNet line + dropshipSaleNetTotal rest

/-- Computes or checks `dropshipSupplierCostTotal` using the validated data in this module. -/
def dropshipSupplierCostTotal : List DropshipLine → Money
  | [] => 0
  | line :: rest => dropshipLineSupplierCost line + dropshipSupplierCostTotal rest

/-- Computes or checks `dropshipWeightTotal` using the validated data in this module. -/
def dropshipWeightTotal : List DropshipLine → Weight
  | [] => 0
  | line :: rest => dropshipLineWeight line + dropshipWeightTotal rest

/-- States the safety property captured by `dropshipSupplierCostTotal_le_saleNetTotal`. -/
theorem dropshipSupplierCostTotal_le_saleNetTotal (lines : List DropshipLine) :
    dropshipSupplierCostTotal lines ≤ dropshipSaleNetTotal lines := by
  induction lines with
  | nil => simp [dropshipSupplierCostTotal, dropshipSaleNetTotal]
  | cons line rest ih =>
      have hline := dropshipLineSupplierCost_le_customerNet line
      simpa [dropshipSupplierCostTotal, dropshipSaleNetTotal] using Nat.add_le_add hline ih

/-- Data shape for `DropshipShippingQuote`; proof fields record invariants when needed. -/
structure DropshipShippingQuote where
  supplierId : SupplierId
  price : Money
  maxWeight : Weight
  carrierDays : Days

/-- Computes or checks `dropshipShippingQuoteCanShip` using the validated data in this module. -/
def dropshipShippingQuoteCanShip (quote : DropshipShippingQuote) (weight : Weight) : Prop :=
  weight ≤ quote.maxWeight

/-- Closed set of cases for `DropshipPOStatus` in the webshop domain model. -/
inductive DropshipPOStatus where
  | Created
  | Submitted
  | Accepted
  | Rejected
  | Shipped
  | Delivered
  | Cancelled
deriving DecidableEq, Repr

/-- Data shape for `DropshipPurchaseOrder`; proof fields record invariants when needed. -/
structure DropshipPurchaseOrder where
  supplier : DropshipSupplier
  lines : List DropshipLine
  quote : DropshipShippingQuote
  status : DropshipPOStatus
  total : Money
  quote_supplier_matches : quote.supplierId = supplier.id
  weight_ok : dropshipWeightTotal lines ≤ quote.maxWeight
  total_correct : total = dropshipSupplierCostTotal lines + quote.price

/-- States the safety property captured by `dropshipPO_total_le_customerNet_plus_supplierShipping`. -/
theorem dropshipPO_total_le_customerNet_plus_supplierShipping (po : DropshipPurchaseOrder) :
    po.total ≤ dropshipSaleNetTotal po.lines + po.quote.price := by
  rw [po.total_correct]
  have hcost := dropshipSupplierCostTotal_le_saleNetTotal po.lines
  exact Nat.add_le_add_right hcost po.quote.price

/-- Computes or checks `CanDropshipPOTransition` using the validated data in this module. -/
def CanDropshipPOTransition : DropshipPOStatus → DropshipPOStatus → Prop
  | DropshipPOStatus.Created, DropshipPOStatus.Submitted => True
  | DropshipPOStatus.Created, DropshipPOStatus.Cancelled => True
  | DropshipPOStatus.Submitted, DropshipPOStatus.Accepted => True
  | DropshipPOStatus.Submitted, DropshipPOStatus.Rejected => True
  | DropshipPOStatus.Submitted, DropshipPOStatus.Cancelled => True
  | DropshipPOStatus.Accepted, DropshipPOStatus.Shipped => True
  | DropshipPOStatus.Accepted, DropshipPOStatus.Cancelled => True
  | DropshipPOStatus.Shipped, DropshipPOStatus.Delivered => True
  | _, _ => False

/-- States the safety property captured by `dropshipPO_cancelled_has_no_outgoing`. -/
theorem dropshipPO_cancelled_has_no_outgoing (next : DropshipPOStatus) :
    ¬ CanDropshipPOTransition DropshipPOStatus.Cancelled next := by
  cases next <;> simp [CanDropshipPOTransition]

/-- Computes or checks `dropshipSLASafe` using the validated data in this module. -/
def dropshipSLASafe (supplier : DropshipSupplier) (quote : DropshipShippingQuote)
    (promisedDays : Days) : Prop :=
  supplier.processingDays + quote.carrierDays ≤ promisedDays

/-- Data shape for `DropshipFulfillment`; proof fields record invariants when needed. -/
structure DropshipFulfillment where
  customerOrder : Order
  purchaseOrder : DropshipPurchaseOrder
  segmentRevenue : Money
  segmentRevenue_correct : segmentRevenue = dropshipSaleNetTotal purchaseOrder.lines
  segmentRevenue_le_order_total : segmentRevenue ≤ customerOrder.total

/-- States the safety property captured by `dropshipFulfillment_supplierCost_le_orderTotal`. -/
theorem dropshipFulfillment_supplierCost_le_orderTotal (f : DropshipFulfillment) :
    dropshipSupplierCostTotal f.purchaseOrder.lines ≤ f.customerOrder.total := by
  calc
    dropshipSupplierCostTotal f.purchaseOrder.lines ≤ dropshipSaleNetTotal f.purchaseOrder.lines :=
      dropshipSupplierCostTotal_le_saleNetTotal f.purchaseOrder.lines
    _ = f.segmentRevenue := f.segmentRevenue_correct.symm
    _ ≤ f.customerOrder.total := f.segmentRevenue_le_order_total

/-- Data shape for `DropshipReturnRequest`; proof fields record invariants when needed. -/
structure DropshipReturnRequest where
  line : DropshipLine
  returnQty : Quantity
  customerRefund : Money
  supplierCredit : Money
  supplier_accepts_returns : line.offer.supplier.acceptsReturns = true
  returnQty_le_soldQty : returnQty ≤ line.quantity
  refund_le_customerNet : customerRefund ≤ dropshipLineCustomerNet line
  supplierCredit_le_supplierCost : supplierCredit ≤ dropshipLineSupplierCost line

/-- States the safety property captured by `dropshipReturn_refund_safe`. -/
theorem dropshipReturn_refund_safe (r : DropshipReturnRequest) :
    r.customerRefund ≤ dropshipLineCustomerNet r.line := by
  exact r.refund_le_customerNet


end WebShopTheoryComplete
