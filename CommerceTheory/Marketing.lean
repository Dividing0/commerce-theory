import CommerceTheory.Marketplace

namespace CommerceTheory

/-! ## 7. Marketing, acquisition, attribution, consent, and experiments -/

/-!
Marketing models spend, attribution, consent, and experiments. The important
guarantees are budget safety, consent-aware messaging, and bounded attribution
credit for an order.
-/

/-- Closed set of cases for `AdPlatform` in the commerce domain model. -/
inductive AdPlatform where
  | GoogleLike
  | MetaLike
  | TikTokLike
  | MarketplaceAds
  | EmailProvider
  | SmsProvider
  | AffiliateNetwork
  | Custom
deriving DecidableEq, Repr

/-- Closed set of cases for `AdType` in the commerce domain model. -/
inductive AdType where
  | Search
  | Shopping
  | Display
  | Social
  | Video
  | Retargeting
  | EmailMarketing
  | SmsMarketing
  | MarketplaceSponsoredProducts
  | Affiliate
deriving DecidableEq, Repr

/-- Closed set of cases for `CampaignStatus` in the commerce domain model. -/
inductive CampaignStatus where
  | Draft
  | Active
  | Paused
  | Archived
deriving DecidableEq, Repr

/-- Closed set of cases for `AdDestination` in the commerce domain model. -/
inductive AdDestination where
  | Website
  | MarketplaceStore : Marketplace → AdDestination
  | MarketplaceListing : Marketplace → Nat → AdDestination
deriving DecidableEq, Repr

/-- Computes or checks `destinationMatchesMarketplace` using the validated data in this module. -/
def destinationMatchesMarketplace (destination : AdDestination) (marketplace : Marketplace) : Prop :=
  match destination with
  | AdDestination.Website => False
  | AdDestination.MarketplaceStore m => m = marketplace
  | AdDestination.MarketplaceListing m _ => m = marketplace

/-- Website destinations never match a marketplace-specific destination. -/
theorem websiteDestination_not_marketplace (marketplace : Marketplace) :
    ¬ destinationMatchesMarketplace AdDestination.Website marketplace := by
  simp [destinationMatchesMarketplace]

/-- Marketplace store destinations match their own marketplace. -/
theorem marketplaceStoreDestination_matches (marketplace : Marketplace) :
    destinationMatchesMarketplace (AdDestination.MarketplaceStore marketplace) marketplace := by
  simp [destinationMatchesMarketplace]

/-- Marketplace listing destinations match their own marketplace. -/
theorem marketplaceListingDestination_matches (marketplace : Marketplace) (externalId : Nat) :
    destinationMatchesMarketplace
      (AdDestination.MarketplaceListing marketplace externalId) marketplace := by
  simp [destinationMatchesMarketplace]

/-- Data shape for `MarketingCampaign`; proof fields record invariants when needed. -/
structure MarketingCampaign where
  id : CampaignId
  platform : AdPlatform
  adType : AdType
  destination : AdDestination
  status : CampaignStatus
  budget : Money
  spend : Money
  impressions : Nat
  clicks : Nat
  conversions : Nat
  attributedRevenue : Money
  spend_le_budget : spend ≤ budget
  clicks_le_impressions : clicks ≤ impressions

/-- States the safety property captured by `campaign_spend_le_budget`. -/
theorem campaign_spend_le_budget (campaign : MarketingCampaign) :
    campaign.spend ≤ campaign.budget := by
  exact campaign.spend_le_budget

/-- Campaign click counts cannot exceed campaign impressions. -/
theorem campaign_clicks_le_impressions (campaign : MarketingCampaign) :
    campaign.clicks ≤ campaign.impressions := by
  exact campaign.clicks_le_impressions

/-- Computes or checks `campaignsSpendTotal` using the validated data in this module. -/
def campaignsSpendTotal : List MarketingCampaign → Money
  | [] => 0
  | c :: rest => c.spend + campaignsSpendTotal rest

/-- Computes or checks `campaignsBudgetTotal` using the validated data in this module. -/
def campaignsBudgetTotal : List MarketingCampaign → Money
  | [] => 0
  | c :: rest => c.budget + campaignsBudgetTotal rest

/-- States the safety property captured by `campaignsSpendTotal_le_campaignsBudgetTotal`. -/
theorem campaignsSpendTotal_le_campaignsBudgetTotal (campaigns : List MarketingCampaign) :
    campaignsSpendTotal campaigns ≤ campaignsBudgetTotal campaigns := by
  induction campaigns with
  | nil => simp [campaignsSpendTotal, campaignsBudgetTotal]
  | cons c rest ih =>
      have hc : c.spend ≤ c.budget := c.spend_le_budget
      simpa [campaignsSpendTotal, campaignsBudgetTotal] using Nat.add_le_add hc ih

/-- Data shape for `ClickAttributedCampaign`; proof fields record invariants when needed. -/
structure ClickAttributedCampaign where
  campaign : MarketingCampaign
  conversions_le_clicks : campaign.conversions ≤ campaign.clicks

/-- States the safety property captured by `clickAttributed_conversions_le_impressions`. -/
theorem clickAttributed_conversions_le_impressions (c : ClickAttributedCampaign) :
    c.campaign.conversions ≤ c.campaign.impressions := by
  have h1 := c.conversions_le_clicks
  have h2 := c.campaign.clicks_le_impressions
  omega

/-- Click-attributed conversions are bounded by clicks. -/
theorem clickAttributed_conversions_le_clicks (c : ClickAttributedCampaign) :
    c.campaign.conversions ≤ c.campaign.clicks := by
  exact c.conversions_le_clicks

/-- Computes or checks `meetsROASTarget` using the validated data in this module. -/
def meetsROASTarget (campaign : MarketingCampaign) (num den : Nat) : Prop :=
  campaign.attributedRevenue * den ≥ campaign.spend * num

/-- A campaign meeting a ROAS target exposes the target inequality. -/
theorem meetsROASTarget_safe
    (campaign : MarketingCampaign) (num den : Nat)
    (h : meetsROASTarget campaign num den) :
    campaign.spend * num ≤ campaign.attributedRevenue * den := by
  exact h

/-- Computes or checks `meetsROITarget` using the validated data in this module. -/
def meetsROITarget (profit adSpend : Money) (num den : Nat) : Prop :=
  profit * den ≥ adSpend * num

/-- A profit/ad-spend pair meeting an ROI target exposes the target inequality. -/
theorem meetsROITarget_safe
    (profit adSpend : Money) (num den : Nat)
    (h : meetsROITarget profit adSpend num den) :
    adSpend * num ≤ profit * den := by
  exact h

/-- Data shape for `Funnel`; proof fields record invariants when needed. -/
structure Funnel where
  visitors : Nat
  addToCart : Nat
  checkoutStarted : Nat
  purchases : Nat
  addToCart_le_visitors : addToCart ≤ visitors
  checkout_le_addToCart : checkoutStarted ≤ addToCart
  purchases_le_checkout : purchases ≤ checkoutStarted

/-- States the safety property captured by `funnel_purchases_le_visitors`. -/
theorem funnel_purchases_le_visitors (f : Funnel) :
    f.purchases ≤ f.visitors := by
  have h1 := f.purchases_le_checkout
  have h2 := f.checkout_le_addToCart
  have h3 := f.addToCart_le_visitors
  omega

/-- Funnel add-to-cart counts are bounded by visitors. -/
theorem funnel_addToCart_le_visitors (f : Funnel) :
    f.addToCart ≤ f.visitors := by
  exact f.addToCart_le_visitors

/-- Funnel checkout starts are bounded by add-to-cart counts. -/
theorem funnel_checkout_le_addToCart (f : Funnel) :
    f.checkoutStarted ≤ f.addToCart := by
  exact f.checkout_le_addToCart

/-- Funnel purchases are bounded by checkout starts. -/
theorem funnel_purchases_le_checkout (f : Funnel) :
    f.purchases ≤ f.checkoutStarted := by
  exact f.purchases_le_checkout

/-- Closed set of cases for `ConsentStatus` in the commerce domain model. -/
inductive ConsentStatus where
  | Granted
  | Denied
  | Unknown
deriving DecidableEq, Repr

/-- Computes or checks `canRetarget` using the validated data in this module. -/
def canRetarget (consent : ConsentStatus) : Prop :=
  consent = ConsentStatus.Granted

/-- States the safety property captured by `denied_consent_cannot_retarget`. -/
theorem denied_consent_cannot_retarget :
    ¬ canRetarget ConsentStatus.Denied := by
  simp [canRetarget]

/-- Unknown consent is not enough to retarget. -/
theorem unknown_consent_cannot_retarget :
    ¬ canRetarget ConsentStatus.Unknown := by
  simp [canRetarget]

/-- Closed set of cases for `SubscriptionStatus` in the commerce domain model. -/
inductive SubscriptionStatus where
  | Subscribed
  | Unsubscribed
deriving DecidableEq, Repr

/-- Computes or checks `canSendMarketingMessage` using the validated data in this module. -/
def canSendMarketingMessage (status : SubscriptionStatus) : Prop :=
  match status with
  | SubscriptionStatus.Subscribed => True
  | SubscriptionStatus.Unsubscribed => False

/-- States the safety property captured by `unsubscribed_cannot_receive_marketing`. -/
theorem unsubscribed_cannot_receive_marketing :
    ¬ canSendMarketingMessage SubscriptionStatus.Unsubscribed := by
  simp [canSendMarketingMessage]

/-- Subscribed customers can receive marketing messages. -/
theorem subscribed_can_receive_marketing :
    canSendMarketingMessage SubscriptionStatus.Subscribed := by
  simp [canSendMarketingMessage]

/-- Data shape for `AttributionCredit`; proof fields record invariants when needed. -/
structure AttributionCredit where
  campaignId : CampaignId
  orderId : OrderId
  amount : Money

/-- Computes or checks `attributionCreditTotal` using the validated data in this module. -/
def attributionCreditTotal : List AttributionCredit → Money
  | [] => 0
  | c :: rest => c.amount + attributionCreditTotal rest

/-- Every attribution credit in a list belongs to the same order. -/
def attributionCreditsMatchOrder (order : Order) (credits : List AttributionCredit) : Prop :=
  ∀ credit : AttributionCredit, credit ∈ credits → credit.orderId = order.id

/-- Data shape for `OrderAttributionLedger`; proof fields record invariants when needed. -/
structure OrderAttributionLedger where
  order : Order
  credits : List AttributionCredit
  total_credits_le_order_total : attributionCreditTotal credits ≤ order.total

/-- An attribution ledger that also validates every credit against the order id. -/
structure MatchedOrderAttributionLedger where
  ledger : OrderAttributionLedger
  credits_match_order : attributionCreditsMatchOrder ledger.order ledger.credits

/-- States the safety property captured by `attributionLedger_total_le_order_total`. -/
theorem attributionLedger_total_le_order_total (l : OrderAttributionLedger) :
    attributionCreditTotal l.credits ≤ l.order.total := by
  exact l.total_credits_le_order_total

/-- Matched attribution ledgers expose per-credit order-id consistency. -/
theorem matchedAttributionLedger_credit_matches_order
    (l : MatchedOrderAttributionLedger)
    (credit : AttributionCredit) (hmem : credit ∈ l.ledger.credits) :
    credit.orderId = l.ledger.order.id := by
  exact l.credits_match_order credit hmem

/-- Matched attribution ledgers still preserve the total-credit bound. -/
theorem matchedAttributionLedger_total_le_order_total
    (l : MatchedOrderAttributionLedger) :
    attributionCreditTotal l.ledger.credits ≤ l.ledger.order.total := by
  exact l.ledger.total_credits_le_order_total

/-- Data shape for `ExperimentVariant`; proof fields record invariants when needed. -/
structure ExperimentVariant where
  id : Id
  trafficWeight : Nat
  visitors : Nat
  conversions : Nat
  conversions_le_visitors : conversions ≤ visitors

/-- Computes or checks `experimentTrafficTotal` using the validated data in this module. -/
def experimentTrafficTotal : List ExperimentVariant → Nat
  | [] => 0
  | v :: rest => v.trafficWeight + experimentTrafficTotal rest

/-- Data shape for `Experiment`; proof fields record invariants when needed. -/
structure Experiment where
  id : Id
  variants : List ExperimentVariant
  traffic_total_100 : experimentTrafficTotal variants = 100

/-- States the safety property captured by `experimentVariant_conversions_safe`. -/
theorem experimentVariant_conversions_safe (v : ExperimentVariant) :
    v.conversions ≤ v.visitors := by
  exact v.conversions_le_visitors

/-- Experiment traffic weights add up to exactly 100. -/
theorem experiment_traffic_total_100 (e : Experiment) :
    experimentTrafficTotal e.variants = 100 := by
  exact e.traffic_total_100


end CommerceTheory
