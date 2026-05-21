import CommerceTheory.PostPurchase

namespace CommerceTheory

/-! ## 18. CRM accounts, contacts, pipeline, support, and retention -/

/-!
CRM objects connect commerce customers to sales, service, and retention flows.
The module keeps operational CRM checks explicit: outreach requires permission,
pipeline value is bounded by gross opportunity value, support resolution keeps
SLA evidence, and retention offers cannot exceed declared value caps.
-/

/-- Closed set of CRM account tiers. -/
inductive AccountTier where
  | Standard
  | Preferred
  | Strategic
deriving DecidableEq, Repr

/-- Closed set of CRM account lifecycle states. -/
inductive CRMAccountStatus where
  | Prospect
  | Active
  | Paused
  | Closed
deriving DecidableEq, Repr

/-- Allowed CRM account lifecycle transitions. -/
inductive CanCRMAccountTransition : CRMAccountStatus → CRMAccountStatus → Prop where
  | prospect_active :
      CanCRMAccountTransition CRMAccountStatus.Prospect CRMAccountStatus.Active
  | prospect_closed :
      CanCRMAccountTransition CRMAccountStatus.Prospect CRMAccountStatus.Closed
  | active_paused :
      CanCRMAccountTransition CRMAccountStatus.Active CRMAccountStatus.Paused
  | active_closed :
      CanCRMAccountTransition CRMAccountStatus.Active CRMAccountStatus.Closed
  | paused_active :
      CanCRMAccountTransition CRMAccountStatus.Paused CRMAccountStatus.Active
  | paused_closed :
      CanCRMAccountTransition CRMAccountStatus.Paused CRMAccountStatus.Closed

/-- Closed CRM accounts are terminal in the modeled account workflow. -/
theorem closedCRMAccount_has_no_outgoing (next : CRMAccountStatus) :
    ¬ CanCRMAccountTransition CRMAccountStatus.Closed next := by
  intro h
  cases h

/-- A CRM account linked to an existing commerce customer profile. -/
structure CRMAccount where
  id : AccountId
  customer : Customer
  tier : AccountTier
  status : CRMAccountStatus
  lifetimeValue : Money
  openBalance : Money
  openBalance_le_lifetimeValue : openBalance ≤ lifetimeValue

/-- CRM accounts never expose an open balance above their recorded lifetime value. -/
theorem crmAccount_openBalance_le_lifetimeValue (account : CRMAccount) :
    account.openBalance ≤ account.lifetimeValue := by
  exact account.openBalance_le_lifetimeValue

/-- Active CRM accounts are accounts currently usable for normal customer operations. -/
def crmAccountActive (account : CRMAccount) : Prop :=
  account.status = CRMAccountStatus.Active

/-- A CRM account that has been validated as active. -/
structure ActiveCRMAccount where
  account : CRMAccount
  active : crmAccountActive account

/-- Active CRM accounts expose their active status. -/
theorem activeCRMAccount_status_active (account : ActiveCRMAccount) :
    account.account.status = CRMAccountStatus.Active := by
  exact account.active

/-- Transition a CRM account while preserving its value safety invariant. -/
def transitionCRMAccount
    (account : CRMAccount)
    (next : CRMAccountStatus)
    (_h : CanCRMAccountTransition account.status next) :
    CRMAccount :=
  { id := account.id
    customer := account.customer
    tier := account.tier
    status := next
    lifetimeValue := account.lifetimeValue
    openBalance := account.openBalance
    openBalance_le_lifetimeValue := account.openBalance_le_lifetimeValue }

/-- CRM account transitions preserve the account identifier. -/
theorem transitionCRMAccount_preserves_id
    (account : CRMAccount) (next : CRMAccountStatus)
    (h : CanCRMAccountTransition account.status next) :
    (transitionCRMAccount account next h).id = account.id := by
  rfl

/-- CRM account transitions preserve open-balance safety. -/
theorem transitionCRMAccount_preserves_balance_safety
    (account : CRMAccount) (next : CRMAccountStatus)
    (h : CanCRMAccountTransition account.status next) :
    (transitionCRMAccount account next h).openBalance ≤
      (transitionCRMAccount account next h).lifetimeValue := by
  exact (transitionCRMAccount account next h).openBalance_le_lifetimeValue

/-- Closed set of contact types attached to a CRM account. -/
inductive ContactKind where
  | Primary
  | Billing
  | Shipping
  | Buyer
  | Support
deriving DecidableEq, Repr

/-- A CRM contact with explicit communication and processing permissions. -/
structure CRMContact where
  id : ContactId
  accountId : AccountId
  customerId : CustomerId
  kind : ContactKind
  ownerRole : Role
  subscription : SubscriptionStatus
  retargetingConsent : ConsentStatus
  dataPermission : DataProcessingPermission

/-- Marketing-style CRM outreach requires subscription, consent, and processing permission. -/
def contactCanReceiveMarketing (contact : CRMContact) : Prop :=
  canSendMarketingMessage contact.subscription ∧
    canRetarget contact.retargetingConsent ∧
    dataProcessingAllowed contact.dataPermission ∧
    contact.dataPermission.purpose = ConsentPurpose.Marketing ∧
    contact.dataPermission.basis = ProcessingBasis.Consent

/-- A CRM account and contact pair whose identifiers have been validated. -/
structure CRMAccountContact where
  account : CRMAccount
  contact : CRMContact
  contact_account_matches : contact.accountId = account.id
  contact_customer_matches : contact.customerId = account.customer.id

/-- Valid CRM account/contact pairs link the contact to the owning account. -/
theorem crmAccountContact_account_matches (x : CRMAccountContact) :
    x.contact.accountId = x.account.id := by
  exact x.contact_account_matches

/-- Valid CRM account/contact pairs link the contact to the commerce customer. -/
theorem crmAccountContact_customer_matches (x : CRMAccountContact) :
    x.contact.customerId = x.account.customer.id := by
  exact x.contact_customer_matches

/-- A permitted CRM message carries all evidence required for customer outreach. -/
structure PermittedCustomerMessage where
  interactionId : InteractionId
  contact : CRMContact
  sentAt : Timestamp
  permitted : contactCanReceiveMarketing contact

/-- Permitted CRM messages can only target subscribed contacts. -/
theorem permittedMessage_subscription_allowed (message : PermittedCustomerMessage) :
    canSendMarketingMessage message.contact.subscription := by
  exact message.permitted.left

/-- Permitted CRM messages can only target contacts with granted retargeting consent. -/
theorem permittedMessage_consent_allowed (message : PermittedCustomerMessage) :
    canRetarget message.contact.retargetingConsent := by
  exact message.permitted.right.left

/-- Permitted CRM messages can only use explicitly allowed data processing. -/
theorem permittedMessage_processing_allowed (message : PermittedCustomerMessage) :
    dataProcessingAllowed message.contact.dataPermission := by
  exact message.permitted.right.right.left

/-- Permitted CRM messages use a marketing data-processing purpose. -/
theorem permittedMessage_marketing_purpose (message : PermittedCustomerMessage) :
    message.contact.dataPermission.purpose = ConsentPurpose.Marketing := by
  exact message.permitted.right.right.right.left

/-- Permitted CRM messages use consent as their processing basis. -/
theorem permittedMessage_consent_basis (message : PermittedCustomerMessage) :
    message.contact.dataPermission.basis = ProcessingBasis.Consent := by
  exact message.permitted.right.right.right.right

/-- A permitted message tied to a validated account/contact pair. -/
structure PermittedAccountMessage where
  accountContact : CRMAccountContact
  message : PermittedCustomerMessage
  message_contact_matches : message.contact = accountContact.contact

/-- Account-scoped permitted messages target the validated CRM contact. -/
theorem permittedAccountMessage_contact_matches (message : PermittedAccountMessage) :
    message.message.contact = message.accountContact.contact := by
  exact message.message_contact_matches

/-- Account-scoped permitted messages inherit the outreach permission gates. -/
theorem permittedAccountMessage_processing_allowed
    (message : PermittedAccountMessage) :
    dataProcessingAllowed message.accountContact.contact.dataPermission := by
  have h := permittedMessage_processing_allowed message.message
  rw [message.message_contact_matches] at h
  exact h

/-- Closed set of CRM interaction types. -/
inductive InteractionKind where
  | Email
  | Call
  | Meeting
  | Chat
  | SupportNote
  | OrderNote
deriving DecidableEq, Repr

/-- CRM interaction records keep follow-up timing ordered after the interaction. -/
structure CRMInteraction where
  id : InteractionId
  accountId : AccountId
  contactId : ContactId
  kind : InteractionKind
  occurredAt : Timestamp
  followUpDueAt : Timestamp
  followUp_after_occurrence : occurredAt ≤ followUpDueAt

/-- CRM follow-up dates cannot precede the interaction they follow. -/
theorem crmInteraction_followUp_after_occurrence (interaction : CRMInteraction) :
    interaction.occurredAt ≤ interaction.followUpDueAt := by
  exact interaction.followUp_after_occurrence

/-- A CRM interaction tied to a validated account/contact pair. -/
structure CRMInteractionForContact where
  accountContact : CRMAccountContact
  interaction : CRMInteraction
  interaction_account_matches : interaction.accountId = accountContact.account.id
  interaction_contact_matches : interaction.contactId = accountContact.contact.id

/-- Validated CRM interactions match the owning account. -/
theorem crmInteractionForContact_account_matches
    (interaction : CRMInteractionForContact) :
    interaction.interaction.accountId = interaction.accountContact.account.id := by
  exact interaction.interaction_account_matches

/-- Validated CRM interactions match the owning contact. -/
theorem crmInteractionForContact_contact_matches
    (interaction : CRMInteractionForContact) :
    interaction.interaction.contactId = interaction.accountContact.contact.id := by
  exact interaction.interaction_contact_matches

/-- Closed set of lead lifecycle states. -/
inductive LeadStatus where
  | New
  | Working
  | Qualified
  | Disqualified
  | Converted
deriving DecidableEq, Repr

/-- Allowed CRM lead state transitions. -/
inductive CanLeadTransition : LeadStatus → LeadStatus → Prop where
  | new_working : CanLeadTransition LeadStatus.New LeadStatus.Working
  | new_disqualified : CanLeadTransition LeadStatus.New LeadStatus.Disqualified
  | working_qualified : CanLeadTransition LeadStatus.Working LeadStatus.Qualified
  | working_disqualified : CanLeadTransition LeadStatus.Working LeadStatus.Disqualified
  | qualified_converted : CanLeadTransition LeadStatus.Qualified LeadStatus.Converted
  | qualified_disqualified : CanLeadTransition LeadStatus.Qualified LeadStatus.Disqualified

/-- Converted leads are terminal in the modeled lead workflow. -/
theorem convertedLead_has_no_outgoing (next : LeadStatus) :
    ¬ CanLeadTransition LeadStatus.Converted next := by
  intro h
  cases h

/-- Disqualified leads are terminal in the modeled lead workflow. -/
theorem disqualifiedLead_has_no_outgoing (next : LeadStatus) :
    ¬ CanLeadTransition LeadStatus.Disqualified next := by
  intro h
  cases h

/-- CRM lead with timestamp ordering and estimated value. -/
structure Lead where
  id : LeadId
  accountId : AccountId
  contactId : ContactId
  sourceCampaign : Option CampaignId
  status : LeadStatus
  estimatedValue : Money
  currency : Currency
  createdAt : Timestamp
  updatedAt : Timestamp
  created_le_updated : createdAt ≤ updatedAt

/-- Lead updates cannot be timestamped before creation. -/
theorem lead_created_le_updated (lead : Lead) :
    lead.createdAt ≤ lead.updatedAt := by
  exact lead.created_le_updated

/-- Transition a lead while preserving account, contact, and creation metadata. -/
def transitionLead
    (lead : Lead)
    (next : LeadStatus)
    (_h : CanLeadTransition lead.status next)
    (updatedAt : Timestamp)
    (hUpdated : lead.createdAt ≤ updatedAt) :
    Lead :=
  { id := lead.id
    accountId := lead.accountId
    contactId := lead.contactId
    sourceCampaign := lead.sourceCampaign
    status := next
    estimatedValue := lead.estimatedValue
    currency := lead.currency
    createdAt := lead.createdAt
    updatedAt := updatedAt
    created_le_updated := hUpdated }

/-- Lead transitions preserve the lead identifier. -/
theorem transitionLead_preserves_id
    (lead : Lead) (next : LeadStatus)
    (h : CanLeadTransition lead.status next)
    (updatedAt : Timestamp) (hUpdated : lead.createdAt ≤ updatedAt) :
    (transitionLead lead next h updatedAt hUpdated).id = lead.id := by
  rfl

/-- Lead transitions preserve timestamp ordering. -/
theorem transitionLead_preserves_timestamp_safety
    (lead : Lead) (next : LeadStatus)
    (h : CanLeadTransition lead.status next)
    (updatedAt : Timestamp) (hUpdated : lead.createdAt ≤ updatedAt) :
    (transitionLead lead next h updatedAt hUpdated).createdAt ≤
      (transitionLead lead next h updatedAt hUpdated).updatedAt := by
  exact (transitionLead lead next h updatedAt hUpdated).created_le_updated

/-- A CRM lead tied to a validated account/contact pair. -/
structure LeadForContact where
  accountContact : CRMAccountContact
  lead : Lead
  lead_account_matches : lead.accountId = accountContact.account.id
  lead_contact_matches : lead.contactId = accountContact.contact.id

/-- Validated CRM leads match the owning account. -/
theorem leadForContact_account_matches (lead : LeadForContact) :
    lead.lead.accountId = lead.accountContact.account.id := by
  exact lead.lead_account_matches

/-- Validated CRM leads match the owning contact. -/
theorem leadForContact_contact_matches (lead : LeadForContact) :
    lead.lead.contactId = lead.accountContact.contact.id := by
  exact lead.lead_contact_matches

/-- Closed set of opportunity pipeline stages. -/
inductive OpportunityStage where
  | Prospecting
  | Qualified
  | Proposal
  | Negotiation
  | Won
  | Lost
deriving DecidableEq, Repr

/-- Allowed CRM opportunity state transitions. -/
inductive CanOpportunityTransition : OpportunityStage → OpportunityStage → Prop where
  | prospecting_qualified :
      CanOpportunityTransition OpportunityStage.Prospecting OpportunityStage.Qualified
  | prospecting_lost :
      CanOpportunityTransition OpportunityStage.Prospecting OpportunityStage.Lost
  | qualified_proposal :
      CanOpportunityTransition OpportunityStage.Qualified OpportunityStage.Proposal
  | qualified_lost :
      CanOpportunityTransition OpportunityStage.Qualified OpportunityStage.Lost
  | proposal_negotiation :
      CanOpportunityTransition OpportunityStage.Proposal OpportunityStage.Negotiation
  | proposal_lost :
      CanOpportunityTransition OpportunityStage.Proposal OpportunityStage.Lost
  | negotiation_won :
      CanOpportunityTransition OpportunityStage.Negotiation OpportunityStage.Won
  | negotiation_lost :
      CanOpportunityTransition OpportunityStage.Negotiation OpportunityStage.Lost

/-- Won opportunities are terminal in the modeled opportunity workflow. -/
theorem wonOpportunity_has_no_outgoing (next : OpportunityStage) :
    ¬ CanOpportunityTransition OpportunityStage.Won next := by
  intro h
  cases h

/-- Lost opportunities are terminal in the modeled opportunity workflow. -/
theorem lostOpportunity_has_no_outgoing (next : OpportunityStage) :
    ¬ CanOpportunityTransition OpportunityStage.Lost next := by
  intro h
  cases h

/-- Stage-level policy for opportunity close probability. -/
def opportunityStageProbabilityAllowed
    (stage : OpportunityStage) (probability : BasisPoints) : Prop :=
  match stage with
  | OpportunityStage.Won => probability.value = 10000
  | OpportunityStage.Lost => probability.value = 0
  | _ => True

/-- A sales opportunity with probability stored as bounded basis points. -/
structure SalesOpportunity where
  id : OpportunityId
  accountId : AccountId
  contactId : ContactId
  sourceLead : Option LeadId
  stage : OpportunityStage
  amount : Money
  currency : Currency
  probability : BasisPoints
  openedAt : Timestamp
  updatedAt : Timestamp
  expectedCloseAt : Timestamp
  opened_le_updated : openedAt ≤ updatedAt
  opened_le_expectedClose : openedAt ≤ expectedCloseAt
  probability_matches_stage : opportunityStageProbabilityAllowed stage probability

/-- Opportunity probabilities respect the stage-level probability policy. -/
theorem opportunity_probability_matches_stage (opportunity : SalesOpportunity) :
    opportunityStageProbabilityAllowed opportunity.stage opportunity.probability := by
  exact opportunity.probability_matches_stage

/-- Weighted pipeline value floors `amount * probability / 10000`. -/
def opportunityWeightedValue (opportunity : SalesOpportunity) : Money :=
  applyBps opportunity.probability opportunity.amount

/-- An opportunity's weighted value never exceeds its gross amount. -/
theorem opportunityWeightedValue_le_amount (opportunity : SalesOpportunity) :
    opportunityWeightedValue opportunity ≤ opportunity.amount := by
  exact applyBps_le_amount opportunity.probability opportunity.amount

/-- Opportunity updates cannot be timestamped before opening. -/
theorem opportunity_opened_le_updated (opportunity : SalesOpportunity) :
    opportunity.openedAt ≤ opportunity.updatedAt := by
  exact opportunity.opened_le_updated

/-- Opportunity expected close dates cannot precede opportunity opening. -/
theorem opportunity_opened_le_expectedClose (opportunity : SalesOpportunity) :
    opportunity.openedAt ≤ opportunity.expectedCloseAt := by
  exact opportunity.opened_le_expectedClose

/-- Transition an opportunity while requiring fresh probability evidence for the next stage. -/
def transitionOpportunity
    (opportunity : SalesOpportunity)
    (next : OpportunityStage)
    (_h : CanOpportunityTransition opportunity.stage next)
    (probability : BasisPoints)
    (hProbability : opportunityStageProbabilityAllowed next probability)
    (updatedAt expectedCloseAt : Timestamp)
    (hUpdated : opportunity.openedAt ≤ updatedAt)
    (hExpected : opportunity.openedAt ≤ expectedCloseAt) :
    SalesOpportunity :=
  { id := opportunity.id
    accountId := opportunity.accountId
    contactId := opportunity.contactId
    sourceLead := opportunity.sourceLead
    stage := next
    amount := opportunity.amount
    currency := opportunity.currency
    probability := probability
    openedAt := opportunity.openedAt
    updatedAt := updatedAt
    expectedCloseAt := expectedCloseAt
    opened_le_updated := hUpdated
    opened_le_expectedClose := hExpected
    probability_matches_stage := hProbability }

/-- Opportunity transitions preserve the opportunity identifier. -/
theorem transitionOpportunity_preserves_id
    (opportunity : SalesOpportunity) (next : OpportunityStage)
    (h : CanOpportunityTransition opportunity.stage next)
    (probability : BasisPoints)
    (hProbability : opportunityStageProbabilityAllowed next probability)
    (updatedAt expectedCloseAt : Timestamp)
    (hUpdated : opportunity.openedAt ≤ updatedAt)
    (hExpected : opportunity.openedAt ≤ expectedCloseAt) :
    (transitionOpportunity opportunity next h probability hProbability
      updatedAt expectedCloseAt hUpdated hExpected).id = opportunity.id := by
  rfl

/-- A sales opportunity tied to a validated account/contact pair. -/
structure OpportunityForContact where
  accountContact : CRMAccountContact
  opportunity : SalesOpportunity
  opportunity_account_matches : opportunity.accountId = accountContact.account.id
  opportunity_contact_matches : opportunity.contactId = accountContact.contact.id

/-- Validated opportunities match the owning account. -/
theorem opportunityForContact_account_matches
    (opportunity : OpportunityForContact) :
    opportunity.opportunity.accountId = opportunity.accountContact.account.id := by
  exact opportunity.opportunity_account_matches

/-- Validated opportunities match the owning contact. -/
theorem opportunityForContact_contact_matches
    (opportunity : OpportunityForContact) :
    opportunity.opportunity.contactId = opportunity.accountContact.contact.id := by
  exact opportunity.opportunity_contact_matches

/-- Sum gross opportunity amounts across a pipeline. -/
def opportunityGrossValue : List SalesOpportunity → Money
  | [] => 0
  | opportunity :: rest => opportunity.amount + opportunityGrossValue rest

/-- Sum probability-weighted opportunity amounts across a pipeline. -/
def opportunityWeightedValueTotal : List SalesOpportunity → Money
  | [] => 0
  | opportunity :: rest => opportunityWeightedValue opportunity + opportunityWeightedValueTotal rest

/-- Aggregate weighted pipeline value cannot exceed aggregate gross pipeline value. -/
theorem opportunityWeightedValueTotal_le_grossValue
    (opportunities : List SalesOpportunity) :
    opportunityWeightedValueTotal opportunities ≤ opportunityGrossValue opportunities := by
  induction opportunities with
  | nil =>
      simp [opportunityWeightedValueTotal, opportunityGrossValue]
  | cons opportunity rest ih =>
      simpa [opportunityWeightedValueTotal, opportunityGrossValue] using
        Nat.add_le_add (opportunityWeightedValue_le_amount opportunity) ih

/-- Every opportunity in a pipeline uses the declared currency. -/
def opportunitiesUseCurrency (currency : Currency) : List SalesOpportunity → Prop
  | [] => True
  | opportunity :: rest =>
      opportunity.currency = currency ∧ opportunitiesUseCurrency currency rest

/-- Currency-consistent opportunity pipelines can be aggregated safely. -/
structure SalesPipeline where
  currency : Currency
  opportunities : List SalesOpportunity
  currency_consistent : opportunitiesUseCurrency currency opportunities

/-- Sales pipelines expose their currency-consistency proof. -/
theorem salesPipeline_currency_consistent (pipeline : SalesPipeline) :
    opportunitiesUseCurrency pipeline.currency pipeline.opportunities := by
  exact pipeline.currency_consistent

/-- Sales pipelines inherit the aggregate weighted-value bound. -/
theorem salesPipeline_weightedValue_le_grossValue (pipeline : SalesPipeline) :
    opportunityWeightedValueTotal pipeline.opportunities ≤
      opportunityGrossValue pipeline.opportunities := by
  exact opportunityWeightedValueTotal_le_grossValue pipeline.opportunities

/-- CRM customer segments bound retention incentives for a customer group. -/
structure CustomerSegment where
  id : SegmentId
  name : String
  memberCount : Nat
  minLifetimeValue : Money
  maxRetentionDiscount : Money
  discount_le_min_lifetime_value : maxRetentionDiscount ≤ minLifetimeValue

/-- Segment-level retention discounts fit inside the segment value floor. -/
theorem segmentRetentionDiscount_le_minLifetimeValue (segment : CustomerSegment) :
    segment.maxRetentionDiscount ≤ segment.minLifetimeValue := by
  exact segment.discount_le_min_lifetime_value

/-- A CRM account assigned to a segment after satisfying its value floor. -/
structure SegmentMembership where
  account : CRMAccount
  segment : CustomerSegment
  account_meets_value_floor : segment.minLifetimeValue ≤ account.lifetimeValue

/-- Segment membership proves the account meets the segment lifetime-value floor. -/
theorem segmentMembership_account_meets_value_floor
    (membership : SegmentMembership) :
    membership.segment.minLifetimeValue ≤ membership.account.lifetimeValue := by
  exact membership.account_meets_value_floor

/-- Closed set of support case priorities. -/
inductive SupportPriority where
  | Low
  | Normal
  | High
  | Urgent
deriving DecidableEq, Repr

/-- Closed set of support case lifecycle states. -/
inductive SupportCaseStatus where
  | Opened
  | WaitingOnCustomer
  | WaitingOnInternal
  | Escalated
  | Resolved
  | Closed
deriving DecidableEq, Repr

/-- Allowed support case state transitions. -/
inductive CanSupportCaseTransition : SupportCaseStatus → SupportCaseStatus → Prop where
  | opened_waiting_customer :
      CanSupportCaseTransition SupportCaseStatus.Opened SupportCaseStatus.WaitingOnCustomer
  | opened_waiting_internal :
      CanSupportCaseTransition SupportCaseStatus.Opened SupportCaseStatus.WaitingOnInternal
  | opened_escalated :
      CanSupportCaseTransition SupportCaseStatus.Opened SupportCaseStatus.Escalated
  | opened_resolved :
      CanSupportCaseTransition SupportCaseStatus.Opened SupportCaseStatus.Resolved
  | waiting_customer_resolved :
      CanSupportCaseTransition SupportCaseStatus.WaitingOnCustomer SupportCaseStatus.Resolved
  | waiting_customer_escalated :
      CanSupportCaseTransition SupportCaseStatus.WaitingOnCustomer SupportCaseStatus.Escalated
  | waiting_internal_resolved :
      CanSupportCaseTransition SupportCaseStatus.WaitingOnInternal SupportCaseStatus.Resolved
  | waiting_internal_escalated :
      CanSupportCaseTransition SupportCaseStatus.WaitingOnInternal SupportCaseStatus.Escalated
  | escalated_resolved :
      CanSupportCaseTransition SupportCaseStatus.Escalated SupportCaseStatus.Resolved
  | resolved_closed :
      CanSupportCaseTransition SupportCaseStatus.Resolved SupportCaseStatus.Closed

/-- Closed support cases are terminal in the modeled support workflow. -/
theorem closedSupportCase_has_no_outgoing (next : SupportCaseStatus) :
    ¬ CanSupportCaseTransition SupportCaseStatus.Closed next := by
  intro h
  cases h

/-- A support case linked to a CRM account and optionally to an order. -/
structure SupportCase where
  id : SupportCaseId
  accountId : AccountId
  contactId : ContactId
  orderId : Option OrderId
  status : SupportCaseStatus
  priority : SupportPriority
  openedAt : Timestamp
  lastUpdatedAt : Timestamp
  slaDueAt : Timestamp
  opened_le_lastUpdated : openedAt ≤ lastUpdatedAt
  opened_le_slaDue : openedAt ≤ slaDueAt

/-- Support cases cannot be last-updated before they were opened. -/
theorem supportCase_opened_le_lastUpdated (case_ : SupportCase) :
    case_.openedAt ≤ case_.lastUpdatedAt := by
  exact case_.opened_le_lastUpdated

/-- Support case SLA due dates cannot precede case opening. -/
theorem supportCase_opened_le_slaDue (case_ : SupportCase) :
    case_.openedAt ≤ case_.slaDueAt := by
  exact case_.opened_le_slaDue

/-- Transition a support case while preserving its identity and SLA due date. -/
def transitionSupportCase
    (case_ : SupportCase)
    (next : SupportCaseStatus)
    (_h : CanSupportCaseTransition case_.status next)
    (updatedAt : Timestamp)
    (hUpdated : case_.openedAt ≤ updatedAt) :
    SupportCase :=
  { id := case_.id
    accountId := case_.accountId
    contactId := case_.contactId
    orderId := case_.orderId
    status := next
    priority := case_.priority
    openedAt := case_.openedAt
    lastUpdatedAt := updatedAt
    slaDueAt := case_.slaDueAt
    opened_le_lastUpdated := hUpdated
    opened_le_slaDue := case_.opened_le_slaDue }

/-- Support case transitions preserve the support case identifier. -/
theorem transitionSupportCase_preserves_id
    (case_ : SupportCase) (next : SupportCaseStatus)
    (h : CanSupportCaseTransition case_.status next)
    (updatedAt : Timestamp) (hUpdated : case_.openedAt ≤ updatedAt) :
    (transitionSupportCase case_ next h updatedAt hUpdated).id = case_.id := by
  rfl

/-- A support case tied to a validated account/contact pair. -/
structure SupportCaseForContact where
  accountContact : CRMAccountContact
  case_ : SupportCase
  case_account_matches : case_.accountId = accountContact.account.id
  case_contact_matches : case_.contactId = accountContact.contact.id

/-- Validated support cases match the owning account. -/
theorem supportCaseForContact_account_matches (case_ : SupportCaseForContact) :
    case_.case_.accountId = case_.accountContact.account.id := by
  exact case_.case_account_matches

/-- Validated support cases match the owning contact. -/
theorem supportCaseForContact_contact_matches (case_ : SupportCaseForContact) :
    case_.case_.contactId = case_.accountContact.contact.id := by
  exact case_.case_contact_matches

/-- A resolved support case that carries SLA evidence. -/
structure ResolvedSupportCase where
  case_ : SupportCase
  resolvedAt : Timestamp
  status_resolved : case_.status = SupportCaseStatus.Resolved
  opened_le_resolved : case_.openedAt ≤ resolvedAt
  lastUpdated_le_resolved : case_.lastUpdatedAt ≤ resolvedAt
  resolved_by_sla : resolvedAt ≤ case_.slaDueAt

/-- Resolved support cases were resolved after they were opened. -/
theorem resolvedSupportCase_opened_le_resolved (case_ : ResolvedSupportCase) :
    case_.case_.openedAt ≤ case_.resolvedAt := by
  exact case_.opened_le_resolved

/-- Resolved support cases carry proof they met the SLA due date. -/
theorem resolvedSupportCase_resolved_by_sla (case_ : ResolvedSupportCase) :
    case_.resolvedAt ≤ case_.case_.slaDueAt := by
  exact case_.resolved_by_sla

/-- Resolved support cases are not resolved before their last update timestamp. -/
theorem resolvedSupportCase_lastUpdated_le_resolved (case_ : ResolvedSupportCase) :
    case_.case_.lastUpdatedAt ≤ case_.resolvedAt := by
  exact case_.lastUpdated_le_resolved

/-- Resolved support cases expose the resolved status. -/
theorem resolvedSupportCase_status_resolved (case_ : ResolvedSupportCase) :
    case_.case_.status = SupportCaseStatus.Resolved := by
  exact case_.status_resolved

/-- Retention offers are capped by both coupon amount and segment policy. -/
structure RetentionOffer where
  account : CRMAccount
  segment : CustomerSegment
  coupon : Coupon
  usesBefore : Nat
  discount : Money
  account_active : crmAccountActive account
  coupon_applicable : couponCanBeApplied coupon account.lifetimeValue usesBefore
  account_meets_segment_value_floor : segment.minLifetimeValue ≤ account.lifetimeValue
  discount_le_coupon : discount ≤ coupon.amount
  coupon_le_lifetimeValue : coupon.amount ≤ account.lifetimeValue
  discount_le_segment_cap : discount ≤ segment.maxRetentionDiscount

/-- Retention discounts fit inside the account lifetime value. -/
theorem retentionOffer_discount_le_lifetimeValue (offer : RetentionOffer) :
    offer.discount ≤ offer.account.lifetimeValue := by
  exact offer.discount_le_coupon.trans offer.coupon_le_lifetimeValue

/-- Retention discounts fit inside the segment retention cap. -/
theorem retentionOffer_discount_le_segment_cap (offer : RetentionOffer) :
    offer.discount ≤ offer.segment.maxRetentionDiscount := by
  exact offer.discount_le_segment_cap

/-- Retention discounts also fit inside the segment lifetime-value floor. -/
theorem retentionOffer_discount_le_segment_value_floor (offer : RetentionOffer) :
    offer.discount ≤ offer.segment.minLifetimeValue := by
  exact offer.discount_le_segment_cap.trans offer.segment.discount_le_min_lifetime_value

/-- Retention offers can only be issued to accounts that satisfy the segment value floor. -/
theorem retentionOffer_account_meets_segment_value_floor (offer : RetentionOffer) :
    offer.segment.minLifetimeValue ≤ offer.account.lifetimeValue := by
  exact offer.account_meets_segment_value_floor

/-- Retention offers can only be issued for active CRM accounts. -/
theorem retentionOffer_account_active (offer : RetentionOffer) :
    offer.account.status = CRMAccountStatus.Active := by
  exact offer.account_active

/-- Retention offer coupons meet their minimum subtotal against account lifetime value. -/
theorem retentionOffer_coupon_minSubtotal_met (offer : RetentionOffer) :
    offer.coupon.minSubtotal ≤ offer.account.lifetimeValue := by
  exact offer.coupon_applicable.left

/-- Retention offer coupons stay below their usage limit. -/
theorem retentionOffer_coupon_usage_below_max (offer : RetentionOffer) :
    offer.usesBefore < offer.coupon.maxUses := by
  exact offer.coupon_applicable.right

end CommerceTheory
