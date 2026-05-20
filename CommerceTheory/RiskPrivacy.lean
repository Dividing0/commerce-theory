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
