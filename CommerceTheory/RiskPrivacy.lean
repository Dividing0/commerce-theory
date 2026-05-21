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

/-! ### Regulatory and compliance controls -/

/-- Personal-data categories used by access and retention policies. -/
inductive DataCategory where
  | CustomerProfile
  | ContactData
  | OrderData
  | PaymentToken
  | MarketingProfile
  | SupportNotes
  | AnalyticsEvent
deriving DecidableEq, Repr

/-- Operational purposes for least-privilege data access. -/
inductive AccessPurpose where
  | CustomerSupport
  | Fulfillment
  | RefundProcessing
  | MarketingOperations
  | FraudReview
  | Analytics
  | Administration
deriving DecidableEq, Repr

/-- Role/category access matrix scoped by purpose. -/
def roleCanAccessData : Role → AccessPurpose → DataCategory → Prop
  | Role.Admin, _, _ => True
  | Role.Support, AccessPurpose.CustomerSupport, DataCategory.OrderData => True
  | Role.Support, AccessPurpose.CustomerSupport, DataCategory.ContactData => True
  | Role.Support, AccessPurpose.CustomerSupport, DataCategory.SupportNotes => True
  | Role.Warehouse, AccessPurpose.Fulfillment, DataCategory.OrderData => True
  | Role.Warehouse, AccessPurpose.Fulfillment, DataCategory.ContactData => True
  | Role.Finance, AccessPurpose.RefundProcessing, DataCategory.OrderData => True
  | Role.Finance, AccessPurpose.RefundProcessing, DataCategory.PaymentToken => True
  | Role.Manager, AccessPurpose.MarketingOperations, DataCategory.MarketingProfile => True
  | Role.Manager, AccessPurpose.MarketingOperations, DataCategory.ContactData => True
  | Role.Manager, AccessPurpose.Administration, DataCategory.CustomerProfile => True
  | Role.Manager, AccessPurpose.Administration, DataCategory.MarketingProfile => True
  | _, _, _ => False

/-- Support can inspect order facts for customer-support work. -/
theorem support_can_view_order_for_support :
    roleCanAccessData Role.Support AccessPurpose.CustomerSupport DataCategory.OrderData := by
  simp [roleCanAccessData]

/-- Support cannot inspect full payment tokens for customer-support work. -/
theorem support_cannot_view_full_payment_token :
    ¬ roleCanAccessData Role.Support AccessPurpose.CustomerSupport DataCategory.PaymentToken := by
  simp [roleCanAccessData]

/-- Finance can access payment-token data in the modeled refund-processing lane. -/
theorem finance_can_view_payment_token_for_refunds :
    roleCanAccessData Role.Finance AccessPurpose.RefundProcessing DataCategory.PaymentToken := by
  simp [roleCanAccessData]

/-- Warehouse fulfillment access excludes customer-profile data. -/
theorem warehouse_cannot_view_customer_profile_for_fulfillment :
    ¬ roleCanAccessData Role.Warehouse AccessPurpose.Fulfillment DataCategory.CustomerProfile := by
  simp [roleCanAccessData]

/--
Data processing may be used only for its declared purpose and legal basis, and
only when the permission is explicitly allowed.
-/
def processingAllowedFor
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (basis : ProcessingBasis) : Prop :=
  dataProcessingAllowed permission ∧
    permission.purpose = purpose ∧
    permission.basis = basis

/-- Purpose-limited processing exposes the declared purpose. -/
theorem processingAllowedFor_declared_purpose
    {permission : DataProcessingPermission}
    {purpose : ConsentPurpose} {basis : ProcessingBasis}
    (h : processingAllowedFor permission purpose basis) :
    permission.purpose = purpose := by
  exact h.right.left

/-- Purpose-limited processing exposes the declared legal basis. -/
theorem processingAllowedFor_declared_basis
    {permission : DataProcessingPermission}
    {purpose : ConsentPurpose} {basis : ProcessingBasis}
    (h : processingAllowedFor permission purpose basis) :
    permission.basis = basis := by
  exact h.right.right

/-- A permission cannot be reused for a different purpose. -/
theorem purpose_limitation_blocks_mismatched_purpose
    (permission : DataProcessingPermission)
    (requested : ConsentPurpose)
    (basis : ProcessingBasis)
    (hMismatch : permission.purpose ≠ requested) :
    ¬ processingAllowedFor permission requested basis := by
  intro h
  exact hMismatch h.right.left

/-- A permission cannot be reused under a different legal basis. -/
theorem processing_basis_limitation_blocks_mismatch
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (requestedBasis : ProcessingBasis)
    (hMismatch : permission.basis ≠ requestedBasis) :
    ¬ processingAllowedFor permission purpose requestedBasis := by
  intro h
  exact hMismatch h.right.right

/-- Marketing consent state combines subscription, retargeting, and processing permission. -/
structure MarketingConsentState where
  subscription : SubscriptionStatus
  retargetingConsent : ConsentStatus
  dataPermission : DataProcessingPermission

/-- Full marketing eligibility across communication, retargeting, and processing gates. -/
def marketingAllowed (state : MarketingConsentState) : Prop :=
  canSendMarketingMessage state.subscription ∧
    canRetarget state.retargetingConsent ∧
    dataProcessingAllowed state.dataPermission ∧
    state.dataPermission.purpose = ConsentPurpose.Marketing ∧
    state.dataPermission.basis = ProcessingBasis.Consent

/-- Withdraw marketing consent and propagate that withdrawal to all marketing gates. -/
def withdrawMarketingConsent (state : MarketingConsentState) : MarketingConsentState :=
  { subscription := SubscriptionStatus.Unsubscribed
    retargetingConsent := ConsentStatus.Denied
    dataPermission :=
      { purpose := state.dataPermission.purpose
        basis := state.dataPermission.basis
        allowed := false } }

/-- Withdrawing consent blocks future marketing messages. -/
theorem consent_withdrawal_blocks_future_marketing
    (state : MarketingConsentState) :
    ¬ marketingAllowed (withdrawMarketingConsent state) := by
  simp [marketingAllowed, withdrawMarketingConsent, canSendMarketingMessage]

/-- Withdrawing consent also blocks retargeting. -/
theorem consent_withdrawal_blocks_retargeting
    (state : MarketingConsentState) :
    ¬ canRetarget (withdrawMarketingConsent state).retargetingConsent := by
  simpa [withdrawMarketingConsent] using denied_consent_cannot_retarget

/-- Withdrawing consent disables the processing permission flag. -/
theorem consent_withdrawal_blocks_data_processing
    (state : MarketingConsentState) :
    ¬ dataProcessingAllowed (withdrawMarketingConsent state).dataPermission := by
  simp [withdrawMarketingConsent, dataProcessingAllowed]

/-- Retention policy for one personal-data category. -/
structure DataRetentionPolicy where
  category : DataCategory
  retentionWindow : Duration

/-- A personal-data record is inside its retention window at `now`. -/
def withinRetentionWindow
    (policy : DataRetentionPolicy) (now collectedAt : Timestamp) : Prop :=
  collectedAt ≤ now ∧ timestampAge now collectedAt ≤ policy.retentionWindow

/-- A personal-data record has exceeded its retention window at `now`. -/
def retentionExpired
    (policy : DataRetentionPolicy) (now collectedAt : Timestamp) : Prop :=
  collectedAt ≤ now ∧ policy.retentionWindow < timestampAge now collectedAt

/-- Retention permission is exactly the modeled retention-window check. -/
def canRetainPersonalData
    (policy : DataRetentionPolicy) (now collectedAt : Timestamp) : Prop :=
  withinRetentionWindow policy now collectedAt

/-- Retained personal data carries retention-window evidence. -/
structure RetainedPersonalData where
  subjectId : CustomerId
  category : DataCategory
  collectedAt : Timestamp
  checkedAt : Timestamp
  policy : DataRetentionPolicy
  category_matches_policy : policy.category = category
  retention_ok : canRetainPersonalData policy checkedAt collectedAt

/-- Retained personal data is inside its configured retention window. -/
theorem retainedPersonalData_within_window
    (record : RetainedPersonalData) :
    withinRetentionWindow record.policy record.checkedAt record.collectedAt := by
  exact record.retention_ok

/-- Expired data cannot be retained under the same policy and clock. -/
theorem expired_personal_data_cannot_be_retained
    (policy : DataRetentionPolicy) (now collectedAt : Timestamp)
    (hExpired : retentionExpired policy now collectedAt) :
    ¬ canRetainPersonalData policy now collectedAt := by
  intro hRetain
  have hWithin : withinRetentionWindow policy now collectedAt := hRetain
  exact (not_lt_of_ge hWithin.right) hExpired.right

/-- Right-to-erasure status for a personal-data subject. -/
inductive ErasureStatus where
  | Active
  | Requested
  | Completed
  | BlockedByLegalHold
deriving DecidableEq, Repr

/-- Personal data is usable for new processing only while the subject is active. -/
def personalDataUsable (status : ErasureStatus) : Prop :=
  status = ErasureStatus.Active

/-- New personal-data processing combines erasure status and purpose limitation. -/
def canProcessPersonalData
    (status : ErasureStatus)
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (basis : ProcessingBasis) : Prop :=
  personalDataUsable status ∧ processingAllowedFor permission purpose basis

/-- An erasure request blocks future personal-data processing. -/
theorem erasure_request_blocks_processing
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (basis : ProcessingBasis) :
    ¬ canProcessPersonalData ErasureStatus.Requested permission purpose basis := by
  simp [canProcessPersonalData, personalDataUsable]

/-- Completed erasure blocks future personal-data processing. -/
theorem completed_erasure_blocks_processing
    (permission : DataProcessingPermission)
    (purpose : ConsentPurpose)
    (basis : ProcessingBasis) :
    ¬ canProcessPersonalData ErasureStatus.Completed permission purpose basis := by
  simp [canProcessPersonalData, personalDataUsable]

/-- Erasure can be completed only when requested and not blocked by legal hold. -/
def canCompleteErasure (status : ErasureStatus) (legalHold : Bool) : Prop :=
  status = ErasureStatus.Requested ∧ legalHold = false

/-- Legal hold blocks right-to-erasure completion. -/
theorem legal_hold_blocks_erasure_completion (status : ErasureStatus) :
    ¬ canCompleteErasure status true := by
  simp [canCompleteErasure]

/-- A compliance audit log is append-only when the new log is the old log plus a suffix. -/
def auditLogAppended
    (before after newEvents : List EntityAuditEvent) : Prop :=
  after = before ++ newEvents

/-- Append-only audit logs preserve every pre-existing audit event. -/
theorem append_only_audit_log_preserves_event
    {before after newEvents : List EntityAuditEvent}
    {event : EntityAuditEvent}
    (hAppend : auditLogAppended before after newEvents)
    (hMem : event ∈ before) :
    event ∈ after := by
  simp [auditLogAppended] at hAppend
  rw [hAppend]
  simp [hMem]

/-- Append-only audit logs cannot shrink. -/
theorem append_only_audit_log_length_ge
    {before after newEvents : List EntityAuditEvent}
    (hAppend : auditLogAppended before after newEvents) :
    before.length ≤ after.length := by
  simp [auditLogAppended] at hAppend
  rw [hAppend, List.length_append]
  exact Nat.le_add_right before.length newEvents.length

/-- Audited data access pairs command permission with purpose-scoped data access. -/
structure AuditedDataAccess where
  actor : Role
  action : Action
  purpose : AccessPurpose
  category : DataCategory
  subjectId : Id
  action_allowed : CanPerform actor action
  data_allowed : roleCanAccessData actor purpose category
  event : EntityAuditEvent
  event_actor_matches : event.actor = actor
  event_action_matches : event.action = action
  event_subject_matches : event.subjectId = subjectId

/-- Audited data access carries its least-privilege proof. -/
theorem auditedDataAccess_least_privilege
    (access : AuditedDataAccess) :
    CanPerform access.actor access.action ∧
      roleCanAccessData access.actor access.purpose access.category := by
  exact ⟨access.action_allowed, access.data_allowed⟩

/-- Audited data access records actor, action, and subject identity. -/
theorem auditedDataAccess_logged
    (access : AuditedDataAccess) :
    access.event.actor = access.actor ∧
      access.event.action = access.action ∧
      access.event.subjectId = access.subjectId := by
  exact ⟨access.event_actor_matches, access.event_action_matches,
    access.event_subject_matches⟩

end CommerceTheory
