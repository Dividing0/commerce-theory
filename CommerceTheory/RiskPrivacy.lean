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
  | ManageCRM
  | CreateSupportCase
  | ResolveSupportCase
  | ManageShipment
  | ApproveReturn
deriving DecidableEq, Repr

/-- Computes or checks `CanPerform` using the validated data in this module. -/
def CanPerform : Role → Action → Prop
  | Role.Admin, _ => True
  | Role.Support, Action.ViewOrder => True
  | Role.Warehouse, Action.PackOrder => True
  | Role.Warehouse, Action.ShipOrder => True
  | Role.Warehouse, Action.AdjustStock => True
  | Role.Warehouse, Action.ManageShipment => True
  | Role.Manager, Action.ViewOrder => True
  | Role.Manager, Action.OverridePrice => True
  | Role.Manager, Action.ManageCRM => True
  | Role.Manager, Action.ResolveSupportCase => True
  | Role.Manager, Action.ApproveReturn => True
  | Role.Support, Action.CreateSupportCase => True
  | Role.Support, Action.ResolveSupportCase => True
  | Role.Support, Action.ManageCRM => True
  | Role.Finance, Action.ViewOrder => True
  | Role.Finance, Action.IssueRefund => True
  | Role.Finance, Action.ApproveReturn => True
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

/-- Support operators can create support cases. -/
theorem support_can_create_support_case :
    CanPerform Role.Support Action.CreateSupportCase := by
  simp [CanPerform]

/-- Finance operators can approve returns, matching refund governance. -/
theorem finance_can_approve_return :
    CanPerform Role.Finance Action.ApproveReturn := by
  simp [CanPerform]

/-- Customers cannot manage CRM records in the access-control relation. -/
theorem customer_cannot_manage_crm :
    ¬ CanPerform Role.Customer Action.ManageCRM := by
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

/-- Entity-scoped audit event for non-order objects such as CRM records and shipments. -/
structure EntityAuditEvent where
  actor : Role
  action : Action
  subjectId : Id

/-- Audited entity command for CRM and logistics operations. -/
structure AuditedEntityCommand where
  actor : Role
  action : Action
  subjectId : Id
  allowed : CanPerform actor action
  event : EntityAuditEvent
  event_actor_matches : event.actor = actor
  event_action_matches : event.action = action
  event_subject_matches : event.subjectId = subjectId

/-- Audited entity commands record the actor that executed the command. -/
theorem auditedEntityCommand_actor_logged (cmd : AuditedEntityCommand) :
    cmd.event.actor = cmd.actor := by
  exact cmd.event_actor_matches

/-- Audited entity commands record the action that was executed. -/
theorem auditedEntityCommand_action_logged (cmd : AuditedEntityCommand) :
    cmd.event.action = cmd.action := by
  exact cmd.event_action_matches

/-- Audited entity commands record the entity they operated on. -/
theorem auditedEntityCommand_subject_logged (cmd : AuditedEntityCommand) :
    cmd.event.subjectId = cmd.subjectId := by
  exact cmd.event_subject_matches

/-- Any audited entity command carries proof that its actor may perform its action. -/
theorem auditedEntityCommand_allowed (cmd : AuditedEntityCommand) :
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

/-- Processing permission is usable only when it has been explicitly allowed. -/
def dataProcessingAllowed (p : DataProcessingPermission) : Prop :=
  p.allowed = true

/-- Explicitly allowed data-processing permissions expose their allow flag. -/
theorem dataProcessingAllowed_is_true
    (p : DataProcessingPermission) (h : dataProcessingAllowed p) :
    p.allowed = true := by
  exact h

/-- Consent-based marketing permission is allowed only when its flag is true. -/
theorem marketingConsentProcessing_requires_allowed_flag
    (p : DataProcessingPermission)
    (_hPurpose : p.purpose = ConsentPurpose.Marketing)
    (_hBasis : p.basis = ProcessingBasis.Consent)
    (h : dataProcessingAllowed p) :
    p.allowed = true := by
  exact h


end CommerceTheory
