import CommerceTheory.FulfillmentFinance

namespace CommerceTheory

/-! ## 14. Risk, fraud, privacy, ABAC, and permissions -/

/-!
Risk and privacy are represented as policy predicates. Access control is an
explicit relation between roles and actions, and audited commands carry proof
that sensitive operations are logged.
-/

/-- Data shape for `FraudPolicy`; proof fields record invariants when needed. -/
structure FraudPolicy where
  maxCouponUses : Nat
  maxOrdersPerHour : Nat
  maxZeroTotalItems : Nat

/-- Computes or checks `couponUsesAllowed` using the validated data in this module. -/
def couponUsesAllowed (policy : FraudPolicy) (uses : Nat) : Prop :=
  uses ≤ policy.maxCouponUses

/-- Computes or checks `ordersPerHourAllowed` using the validated data in this module. -/
def ordersPerHourAllowed (policy : FraudPolicy) (ordersPerHour : Nat) : Prop :=
  ordersPerHour ≤ policy.maxOrdersPerHour

/-- States the safety property captured by `couponUses_do_not_exceed_limit`. -/
theorem couponUses_do_not_exceed_limit
    (policy : FraudPolicy) (uses : Nat) (h : couponUsesAllowed policy uses) :
    uses ≤ policy.maxCouponUses := by
  exact h

/-- Accepted order velocity stays within the fraud policy's hourly limit. -/
theorem ordersPerHour_do_not_exceed_limit
    (policy : FraudPolicy) (ordersPerHour : Nat)
    (h : ordersPerHourAllowed policy ordersPerHour) :
    ordersPerHour ≤ policy.maxOrdersPerHour := by
  exact h

/-- Closed set of cases for `Role` in the commerce domain model. -/
inductive Role where
  | Customer
  | Support
  | Warehouse
  | Manager
  | Finance
  | Admin
deriving DecidableEq, Repr

/-- Closed set of cases for `Action` in the commerce domain model. -/
inductive Action where
  | ViewOrder
  | PackOrder
  | ShipOrder
  | IssueRefund
  | OverridePrice
  | AdjustStock
  | DeleteOrder
deriving DecidableEq, Repr

/-- Computes or checks `CanPerform` using the validated data in this module. -/
def CanPerform : Role → Action → Prop
  | Role.Admin, _ => True
  | Role.Support, Action.ViewOrder => True
  | Role.Warehouse, Action.PackOrder => True
  | Role.Warehouse, Action.ShipOrder => True
  | Role.Warehouse, Action.AdjustStock => True
  | Role.Manager, Action.ViewOrder => True
  | Role.Manager, Action.OverridePrice => True
  | Role.Finance, Action.ViewOrder => True
  | Role.Finance, Action.IssueRefund => True
  | _, _ => False

/-- States the safety property captured by `deleteOrder_requires_admin`. -/
theorem deleteOrder_requires_admin (role : Role) (h : CanPerform role Action.DeleteOrder) :
    role = Role.Admin := by
  cases role <;> simp [CanPerform] at h ⊢

/-- Administrators can perform every modeled action. -/
theorem admin_can_perform (action : Action) :
    CanPerform Role.Admin action := by
  cases action <;> simp [CanPerform]

/-- Customers cannot issue refunds in the access-control relation. -/
theorem customer_cannot_issue_refund :
    ¬ CanPerform Role.Customer Action.IssueRefund := by
  simp [CanPerform]

/-- Warehouse operators can adjust stock, matching their operational boundary. -/
theorem warehouse_can_adjust_stock :
    CanPerform Role.Warehouse Action.AdjustStock := by
  simp [CanPerform]

/-- Data shape for `AuditEvent`; proof fields record invariants when needed. -/
structure AuditEvent where
  actor : Role
  action : Action
  orderId : OrderId

/-- Data shape for `AuditedCommand`; proof fields record invariants when needed. -/
structure AuditedCommand where
  actor : Role
  action : Action
  orderId : OrderId
  allowed : CanPerform actor action
  event : AuditEvent
  event_actor_matches : event.actor = actor
  event_action_matches : event.action = action
  event_order_matches : event.orderId = orderId

/-- States the safety property captured by `auditedCommand_action_logged`. -/
theorem auditedCommand_action_logged (cmd : AuditedCommand) :
    cmd.event.action = cmd.action := by
  exact cmd.event_action_matches

/-- Audited commands record the actor that executed the command. -/
theorem auditedCommand_actor_logged (cmd : AuditedCommand) :
    cmd.event.actor = cmd.actor := by
  exact cmd.event_actor_matches

/-- Audited commands record the order they operated on. -/
theorem auditedCommand_order_logged (cmd : AuditedCommand) :
    cmd.event.orderId = cmd.orderId := by
  exact cmd.event_order_matches

/-- Any audited command carries proof that its actor may perform its action. -/
theorem auditedCommand_allowed (cmd : AuditedCommand) :
    CanPerform cmd.actor cmd.action := by
  exact cmd.allowed

/-- Closed set of cases for `ConsentPurpose` in the commerce domain model. -/
inductive ConsentPurpose where
  | Marketing
  | Analytics
  | Personalization
  | FraudPrevention
deriving DecidableEq, Repr

/-- Closed set of cases for `ProcessingBasis` in the commerce domain model. -/
inductive ProcessingBasis where
  | Consent
  | Contract
  | LegalObligation
  | LegitimateInterest
deriving DecidableEq, Repr

/-- Data shape for `DataProcessingPermission`; proof fields record invariants when needed. -/
structure DataProcessingPermission where
  purpose : ConsentPurpose
  basis : ProcessingBasis
  allowed : Bool


end CommerceTheory
