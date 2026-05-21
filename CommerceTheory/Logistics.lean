import CommerceTheory.CRM
import CommerceTheory.Forecasting

namespace CommerceTheory

/-! ## 19. Logistics shipment planning, tracking, transfers, and returns -/

/-!
Logistics joins orders, inventory, carrier quotes, warehouses, tracking events,
and CRM support cases. The validated records prove that shipment plans fit
carrier capacity, delivery evidence meets promises, transfers do not overdraw
source stock, and return authorizations stay inside order and refund bounds.
-/

/-- Closed set of logistics shipment lifecycle states. -/
inductive ShipmentStatus where
  | Planned
  | Allocated
  | Packed
  | InTransit
  | OutForDelivery
  | Delivered
  | Exception
  | Returned
  | Cancelled
deriving DecidableEq, Repr

/-- Allowed logistics shipment state transitions. -/
inductive CanShipmentTransition : ShipmentStatus → ShipmentStatus → Prop where
  | planned_allocated :
      CanShipmentTransition ShipmentStatus.Planned ShipmentStatus.Allocated
  | planned_cancelled :
      CanShipmentTransition ShipmentStatus.Planned ShipmentStatus.Cancelled
  | allocated_packed :
      CanShipmentTransition ShipmentStatus.Allocated ShipmentStatus.Packed
  | allocated_cancelled :
      CanShipmentTransition ShipmentStatus.Allocated ShipmentStatus.Cancelled
  | packed_inTransit :
      CanShipmentTransition ShipmentStatus.Packed ShipmentStatus.InTransit
  | inTransit_outForDelivery :
      CanShipmentTransition ShipmentStatus.InTransit ShipmentStatus.OutForDelivery
  | inTransit_exception :
      CanShipmentTransition ShipmentStatus.InTransit ShipmentStatus.Exception
  | outForDelivery_delivered :
      CanShipmentTransition ShipmentStatus.OutForDelivery ShipmentStatus.Delivered
  | outForDelivery_exception :
      CanShipmentTransition ShipmentStatus.OutForDelivery ShipmentStatus.Exception
  | exception_inTransit :
      CanShipmentTransition ShipmentStatus.Exception ShipmentStatus.InTransit
  | exception_returned :
      CanShipmentTransition ShipmentStatus.Exception ShipmentStatus.Returned

/-- Delivered shipments are terminal in the modeled shipment workflow. -/
theorem deliveredShipmentStatus_has_no_outgoing (next : ShipmentStatus) :
    ¬ CanShipmentTransition ShipmentStatus.Delivered next := by
  intro h
  cases h

/-- Cancelled shipments are terminal in the modeled shipment workflow. -/
theorem cancelledShipmentStatus_has_no_outgoing (next : ShipmentStatus) :
    ¬ CanShipmentTransition ShipmentStatus.Cancelled next := by
  intro h
  cases h

/-- Returned shipments are terminal in the modeled shipment workflow. -/
theorem returnedShipmentStatus_has_no_outgoing (next : ShipmentStatus) :
    ¬ CanShipmentTransition ShipmentStatus.Returned next := by
  intro h
  cases h

/-- Orders are eligible for outbound logistics only after payment and before shipment. -/
def orderEligibleForLogistics (order : Order) : Prop :=
  order.status = OrderStatus.Paid ∨ order.status = OrderStatus.Packed

/-- Shipment plan tying an order to fulfillment allocations and a carrier quote. -/
structure LogisticsShipmentPlan where
  id : ShipmentId
  order : Order
  fulfillment : FulfillmentPlan
  package : Package
  quote : CarrierQuote
  warehouse : Warehouse
  plannedShipAt : Timestamp
  promisedDeliveryAt : Timestamp
  order_eligible : orderEligibleForLogistics order
  quantity_matches_cart : fulfillment.requested = cartQuantityTotal order.items
  quote_package_matches : quote.package = package
  package_covers_cart_weight : cartWeightTotal order.items ≤ package.weight
  planned_le_promised : plannedShipAt ≤ promisedDeliveryAt

/-- Shipment plans only target orders eligible for outbound logistics. -/
theorem shipmentPlan_order_eligible (plan : LogisticsShipmentPlan) :
    orderEligibleForLogistics plan.order := by
  exact plan.order_eligible

/-- Shipment plans expose that allocated quantity equals cart quantity. -/
theorem shipmentPlan_quantity_matches_cart (plan : LogisticsShipmentPlan) :
    plan.fulfillment.requested = cartQuantityTotal plan.order.items := by
  exact plan.quantity_matches_cart

/-- Shipment plans inherit the fulfillment allocation stock bound. -/
theorem shipmentPlan_requested_le_availableTotal (plan : LogisticsShipmentPlan) :
    plan.fulfillment.requested ≤ allocationsAvailableTotal plan.fulfillment.allocations := by
  exact fulfillmentPlan_requested_le_availableTotal plan.fulfillment

/-- Shipment packages fit inside the selected carrier service capacity. -/
theorem shipmentPlan_package_weight_safe (plan : LogisticsShipmentPlan) :
    plan.package.weight ≤ plan.quote.service.maxWeight := by
  rw [← plan.quote_package_matches]
  exact plan.quote.package_weight_ok

/-- Shipment package weight covers the order's cart weight. -/
theorem shipmentPlan_package_covers_cart_weight (plan : LogisticsShipmentPlan) :
    cartWeightTotal plan.order.items ≤ plan.package.weight := by
  exact plan.package_covers_cart_weight

/-- Shipment quote prices cover the configured carrier service base cost. -/
theorem shipmentPlan_quote_price_covers_base_cost (plan : LogisticsShipmentPlan) :
    plan.quote.service.baseCost ≤ plan.quote.price := by
  exact carrierQuote_price_covers_base_cost plan.quote

/-- Shipment plans do not promise delivery before the planned ship time. -/
theorem shipmentPlan_planned_le_promised (plan : LogisticsShipmentPlan) :
    plan.plannedShipAt ≤ plan.promisedDeliveryAt := by
  exact plan.planned_le_promised

/-- A concrete shipment instance with current lifecycle status. -/
structure LogisticsShipment where
  id : ShipmentId
  plan : LogisticsShipmentPlan
  status : ShipmentStatus
  createdAt : Timestamp
  updatedAt : Timestamp
  id_matches_plan : id = plan.id
  created_le_updated : createdAt ≤ updatedAt

/-- Concrete shipments keep their id synchronized with the shipment plan. -/
theorem logisticsShipment_id_matches_plan (shipment : LogisticsShipment) :
    shipment.id = shipment.plan.id := by
  exact shipment.id_matches_plan

/-- Concrete shipment updates cannot precede shipment creation. -/
theorem logisticsShipment_created_le_updated (shipment : LogisticsShipment) :
    shipment.createdAt ≤ shipment.updatedAt := by
  exact shipment.created_le_updated

/-- Carrier handoff records the first accepted carrier scan. -/
structure CarrierHandoff where
  plan : LogisticsShipmentPlan
  service : CarrierService
  handedOffAt : Timestamp
  acceptanceScanAt : Timestamp
  service_matches_quote : service = plan.quote.service
  plannedShip_le_handedOff : plan.plannedShipAt ≤ handedOffAt
  handedOff_le_acceptanceScan : handedOffAt ≤ acceptanceScanAt

/-- Carrier handoffs use the same service as the selected quote. -/
theorem carrierHandoff_service_matches_quote (handoff : CarrierHandoff) :
    handoff.service = handoff.plan.quote.service := by
  exact handoff.service_matches_quote

/-- Carrier acceptance scans cannot precede handoff. -/
theorem carrierHandoff_handedOff_le_acceptanceScan (handoff : CarrierHandoff) :
    handoff.handedOffAt ≤ handoff.acceptanceScanAt := by
  exact handoff.handedOff_le_acceptanceScan

/-- Carrier handoffs cannot precede the shipment plan's ship timestamp. -/
theorem carrierHandoff_plannedShip_le_handedOff (handoff : CarrierHandoff) :
    handoff.plan.plannedShipAt ≤ handoff.handedOffAt := by
  exact handoff.plannedShip_le_handedOff

/-- Closed set of tracking event kinds. -/
inductive TrackingEventKind where
  | LabelCreated
  | PickupScan
  | InTransitScan
  | OutForDeliveryScan
  | DeliveredScan
  | ExceptionScan
  | ReturnScan
deriving DecidableEq, Repr

/-- A timestamped carrier or warehouse tracking event. -/
structure TrackingEvent where
  id : TrackingEventId
  shipmentId : ShipmentId
  kind : TrackingEventKind
  occurredAt : Timestamp

/-- Tracking events are monotone when each timestamp is no older than the prior cursor. -/
def trackingEventsMonotoneFrom : Timestamp → List TrackingEvent → Prop
  | _last, [] => True
  | last, event :: rest =>
      last ≤ event.occurredAt ∧ trackingEventsMonotoneFrom event.occurredAt rest

/-- Tracking events all belong to the requested shipment id. -/
def trackingEventsForShipment (shipmentId : ShipmentId) : List TrackingEvent → Prop
  | [] => True
  | event :: rest =>
      event.shipmentId = shipmentId ∧ trackingEventsForShipment shipmentId rest

/-- Fold the last observed tracking timestamp out of a tracking event list. -/
def trackingLastObservedFrom : Timestamp → List TrackingEvent → Timestamp
  | last, [] => last
  | _, event :: rest => trackingLastObservedFrom event.occurredAt rest

/-- Ordered nonempty tracking histories expose the first timestamp bound. -/
theorem trackingEventsMonotoneFrom_head
    (last : Timestamp) (event : TrackingEvent) (rest : List TrackingEvent)
    (h : trackingEventsMonotoneFrom last (event :: rest)) :
    last ≤ event.occurredAt := by
  exact h.left

/-- Shipment-specific nonempty tracking histories expose the first shipment id. -/
theorem trackingEventsForShipment_head
    (shipmentId : ShipmentId) (event : TrackingEvent) (rest : List TrackingEvent)
    (h : trackingEventsForShipment shipmentId (event :: rest)) :
    event.shipmentId = shipmentId := by
  exact h.left

/-- Tracking history with monotone timestamps and a computed cursor. -/
structure TrackingHistory where
  shipmentId : ShipmentId
  events : List TrackingEvent
  lastObservedAt : Timestamp
  events_monotone : trackingEventsMonotoneFrom 0 events
  events_match_shipment : trackingEventsForShipment shipmentId events
  lastObserved_correct : lastObservedAt = trackingLastObservedFrom 0 events

/-- Tracking histories expose their monotone timestamp guarantee. -/
theorem trackingHistory_events_monotone (history : TrackingHistory) :
    trackingEventsMonotoneFrom 0 history.events := by
  exact history.events_monotone

/-- Tracking histories expose that every event belongs to the tracked shipment. -/
theorem trackingHistory_events_match_shipment (history : TrackingHistory) :
    trackingEventsForShipment history.shipmentId history.events := by
  exact history.events_match_shipment

/-- Tracking histories store the cursor computed from their events. -/
theorem trackingHistory_lastObserved_correct (history : TrackingHistory) :
    history.lastObservedAt = trackingLastObservedFrom 0 history.events := by
  exact history.lastObserved_correct

/-- A delivery promise derived from the shipment plan. -/
structure DeliveryPromise where
  plan : LogisticsShipmentPlan
  promisedBy : Timestamp
  promised_matches_plan : promisedBy = plan.promisedDeliveryAt

/-- Delivered-by-promise is the core delivery SLA predicate. -/
def deliveredByPromise (promise : DeliveryPromise) (deliveredAt : Timestamp) : Prop :=
  deliveredAt ≤ promise.promisedBy

/-- A delivered shipment with tracking and promised-window evidence. -/
structure DeliveredShipment where
  promise : DeliveryPromise
  history : TrackingHistory
  deliveryEvent : TrackingEvent
  deliveredAt : Timestamp
  history_matches_shipment : history.shipmentId = promise.plan.id
  delivery_event_in_history : deliveryEvent ∈ history.events
  delivery_event_kind : deliveryEvent.kind = TrackingEventKind.DeliveredScan
  delivery_event_time : deliveryEvent.occurredAt = deliveredAt
  delivery_event_shipment : deliveryEvent.shipmentId = promise.plan.id
  shipped_le_delivered : promise.plan.plannedShipAt ≤ deliveredAt
  delivered_by_promise : deliveredByPromise promise deliveredAt

/-- Delivered shipments cannot precede their planned ship timestamp. -/
theorem deliveredShipment_shipped_le_delivered (shipment : DeliveredShipment) :
    shipment.promise.plan.plannedShipAt ≤ shipment.deliveredAt := by
  exact shipment.shipped_le_delivered

/-- Delivered shipments meet their delivery promise. -/
theorem deliveredShipment_delivered_by_promise (shipment : DeliveredShipment) :
    deliveredByPromise shipment.promise shipment.deliveredAt := by
  exact shipment.delivered_by_promise

/-- Delivered shipments arrive by the shipment plan's promised delivery timestamp. -/
theorem deliveredShipment_deliveredAt_le_plan_promised (shipment : DeliveredShipment) :
    shipment.deliveredAt ≤ shipment.promise.plan.promisedDeliveryAt := by
  simpa [deliveredByPromise, shipment.promise.promised_matches_plan] using
    shipment.delivered_by_promise

/-- Delivered shipments include an actual delivered tracking scan. -/
theorem deliveredShipment_has_delivered_scan (shipment : DeliveredShipment) :
    shipment.deliveryEvent.kind = TrackingEventKind.DeliveredScan ∧
      shipment.deliveryEvent.occurredAt = shipment.deliveredAt ∧
      shipment.deliveryEvent.shipmentId = shipment.promise.plan.id ∧
      shipment.deliveryEvent ∈ shipment.history.events := by
  exact ⟨shipment.delivery_event_kind, shipment.delivery_event_time,
    shipment.delivery_event_shipment, shipment.delivery_event_in_history⟩

/-- Closed set of logistics exception kinds. -/
inductive LogisticsExceptionKind where
  | CarrierDelay
  | WeatherDelay
  | AddressIssue
  | LostPackage
  | DamagedPackage
  | CustomerUnavailable
deriving DecidableEq, Repr

/-- Logistics exception records can later be escalated to CRM support. -/
structure LogisticsException where
  shipmentId : ShipmentId
  kind : LogisticsExceptionKind
  raisedAt : Timestamp
  customerVisible : Bool

/-- Warehouse transfer with source-stock and receiving bounds. -/
structure WarehouseTransfer where
  id : TransferId
  sku : Sku
  fromWarehouse : Warehouse
  toWarehouse : Warehouse
  sourceStock : StockState
  requested : Quantity
  inTransit : Quantity
  received : Quantity
  source_sku_matches : sourceStock.sku = sku
  warehouses_distinct : fromWarehouse.id ≠ toWarehouse.id
  requested_le_available : requested ≤ availableStock sourceStock
  inTransit_le_requested : inTransit ≤ requested
  received_le_inTransit : received ≤ inTransit

/-- Warehouse transfers cannot request more than source available stock. -/
theorem warehouseTransfer_requested_le_available (transfer : WarehouseTransfer) :
    transfer.requested ≤ availableStock transfer.sourceStock := by
  exact transfer.requested_le_available

/-- Warehouse transfers cannot receive more than the in-transit quantity. -/
theorem warehouseTransfer_received_le_inTransit (transfer : WarehouseTransfer) :
    transfer.received ≤ transfer.inTransit := by
  exact transfer.received_le_inTransit

/-- Warehouse transfers cannot receive more than the requested quantity. -/
theorem warehouseTransfer_received_le_requested (transfer : WarehouseTransfer) :
    transfer.received ≤ transfer.requested := by
  exact transfer.received_le_inTransit.trans transfer.inTransit_le_requested

/-- Warehouse transfer source stock matches the transferred SKU. -/
theorem warehouseTransfer_source_sku_matches (transfer : WarehouseTransfer) :
    transfer.sourceStock.sku = transfer.sku := by
  exact transfer.source_sku_matches

/-- Warehouse transfers move stock between distinct warehouse ids. -/
theorem warehouseTransfer_warehouses_distinct (transfer : WarehouseTransfer) :
    transfer.fromWarehouse.id ≠ transfer.toWarehouse.id := by
  exact transfer.warehouses_distinct

/-- Closed set of return authorization lifecycle states. -/
inductive ReturnAuthorizationStatus where
  | Requested
  | Approved
  | Rejected
  | Received
  | Refunded
  | Closed
deriving DecidableEq, Repr

/-- Allowed return authorization state transitions. -/
inductive CanReturnAuthorizationTransition :
    ReturnAuthorizationStatus → ReturnAuthorizationStatus → Prop where
  | requested_approved :
      CanReturnAuthorizationTransition
        ReturnAuthorizationStatus.Requested ReturnAuthorizationStatus.Approved
  | requested_rejected :
      CanReturnAuthorizationTransition
        ReturnAuthorizationStatus.Requested ReturnAuthorizationStatus.Rejected
  | approved_received :
      CanReturnAuthorizationTransition
        ReturnAuthorizationStatus.Approved ReturnAuthorizationStatus.Received
  | received_refunded :
      CanReturnAuthorizationTransition
        ReturnAuthorizationStatus.Received ReturnAuthorizationStatus.Refunded
  | refunded_closed :
      CanReturnAuthorizationTransition
        ReturnAuthorizationStatus.Refunded ReturnAuthorizationStatus.Closed

/-- Rejected return authorizations are terminal in the modeled return workflow. -/
theorem rejectedReturnAuthorization_has_no_outgoing
    (next : ReturnAuthorizationStatus) :
    ¬ CanReturnAuthorizationTransition ReturnAuthorizationStatus.Rejected next := by
  intro h
  cases h

/-- Closed return authorizations are terminal in the modeled return workflow. -/
theorem closedReturnAuthorization_has_no_outgoing
    (next : ReturnAuthorizationStatus) :
    ¬ CanReturnAuthorizationTransition ReturnAuthorizationStatus.Closed next := by
  intro h
  cases h

/-- Return authorization linked to a support case, order, and refund ledger. -/
structure ReturnAuthorization where
  id : ReturnAuthorizationId
  supportCase : SupportCase
  order : Order
  ledger : PaymentLedger
  status : ReturnAuthorizationStatus
  quantity : Quantity
  refundAmount : Money
  requestedAt : Timestamp
  decidedAt : Timestamp
  support_case_matches_order : supportCase.orderId = some order.id
  quantity_le_order_quantity : quantity ≤ cartQuantityTotal order.items
  refundable : canRefund ledger refundAmount
  captured_matches_order_total : ledger.captured = order.total
  requested_le_decided : requestedAt ≤ decidedAt

/-- Predicate for return authorizations approved by CRM/service operations. -/
def returnAuthorizationApproved (authorization : ReturnAuthorization) : Prop :=
  authorization.status = ReturnAuthorizationStatus.Approved

/-- Return authorization quantities fit inside the original order quantity. -/
theorem returnAuthorization_quantity_le_order_quantity
    (authorization : ReturnAuthorization) :
    authorization.quantity ≤ cartQuantityTotal authorization.order.items := by
  exact authorization.quantity_le_order_quantity

/-- Return authorization refunds fit inside the remaining refundable ledger amount. -/
theorem returnAuthorization_refund_le_remaining
    (authorization : ReturnAuthorization) :
    authorization.refundAmount ≤ remainingRefundAmount authorization.ledger := by
  exact canRefund_amount_le_remaining
    authorization.ledger authorization.refundAmount authorization.refundable

/-- Return authorization refunds also fit inside the original order total. -/
theorem returnAuthorization_refund_le_order_total
    (authorization : ReturnAuthorization) :
    authorization.refundAmount ≤ authorization.order.total := by
  have hRemaining : authorization.refundAmount ≤
      remainingRefundAmount authorization.ledger :=
    returnAuthorization_refund_le_remaining authorization
  have hRemainingLeCaptured :
      remainingRefundAmount authorization.ledger ≤ authorization.ledger.captured := by
    unfold remainingRefundAmount
    exact Nat.sub_le authorization.ledger.captured authorization.ledger.refunded
  exact hRemaining.trans
    (by
      rw [authorization.captured_matches_order_total] at hRemainingLeCaptured
      exact hRemainingLeCaptured)

/-- Return authorization support cases point at the returned order. -/
theorem returnAuthorization_support_case_matches_order
    (authorization : ReturnAuthorization) :
    authorization.supportCase.orderId = some authorization.order.id := by
  exact authorization.support_case_matches_order

/-- Return authorization decisions cannot precede the request. -/
theorem returnAuthorization_requested_le_decided
    (authorization : ReturnAuthorization) :
    authorization.requestedAt ≤ authorization.decidedAt := by
  exact authorization.requested_le_decided

/-- Physical return receipt remains within the approved authorization. -/
structure ReturnReceipt where
  authorization : ReturnAuthorization
  receivedQuantity : Quantity
  refundIssued : Money
  receivedAt : Timestamp
  received_le_authorized : receivedQuantity ≤ authorization.quantity
  refund_le_authorized : refundIssued ≤ authorization.refundAmount
  decided_le_received : authorization.decidedAt ≤ receivedAt

/-- Return receipts cannot receive more units than authorized. -/
theorem returnReceipt_received_le_order_quantity (receipt : ReturnReceipt) :
    receipt.receivedQuantity ≤ cartQuantityTotal receipt.authorization.order.items := by
  exact receipt.received_le_authorized.trans
    receipt.authorization.quantity_le_order_quantity

/-- Return receipt refunds stay within the authorized refund amount. -/
theorem returnReceipt_refund_le_authorized (receipt : ReturnReceipt) :
    receipt.refundIssued ≤ receipt.authorization.refundAmount := by
  exact receipt.refund_le_authorized

/-- Return receipt refunds fit inside the remaining refundable ledger amount. -/
theorem returnReceipt_refund_le_remaining (receipt : ReturnReceipt) :
    receipt.refundIssued ≤ remainingRefundAmount receipt.authorization.ledger := by
  exact receipt.refund_le_authorized.trans
    (returnAuthorization_refund_le_remaining receipt.authorization)

/-- Return receipt refunds fit inside the original order total. -/
theorem returnReceipt_refund_le_order_total (receipt : ReturnReceipt) :
    receipt.refundIssued ≤ receipt.authorization.order.total := by
  exact receipt.refund_le_authorized.trans
    (returnAuthorization_refund_le_order_total receipt.authorization)

/-- Return receipts cannot be recorded before the return authorization decision. -/
theorem returnReceipt_decided_le_received (receipt : ReturnReceipt) :
    receipt.authorization.decidedAt ≤ receipt.receivedAt := by
  exact receipt.decided_le_received

end CommerceTheory
