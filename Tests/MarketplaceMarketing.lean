import CommerceTheory.Marketing
import CommerceTheory.Marketplace

namespace CommerceTheory.Tests

def marketplaceMarketingSku : Sku :=
  { value := 7101 }

def marketplaceMarketingBasisPoints10Percent : BasisPoints :=
  { value := 1000
    value_le_10000 := by norm_num }

def marketplaceMarketingListing : MarketplaceListing :=
  { sku := marketplaceMarketingSku
    marketplace := Marketplace.EtsyLike
    externalId := 55
    price := 1500
    currency := Currency.USD
    publishedStock := 4
    status := ListingStatus.Active }

def marketplaceExamplesPass : Bool :=
  marketplaceFeeRounded RoundingMode.Floor 10000 marketplaceMarketingBasisPoints10Percent == 1000 &&
    marketplacePayoutRounded RoundingMode.Ceiling 9999 marketplaceMarketingBasisPoints10Percent == 1000

example : listingCanBeAdvertised marketplaceMarketingListing := by
  simp [
    listingCanBeAdvertised,
    listingActive,
    listingInStock,
    marketplaceMarketingListing
  ]

def marketingCampaignExample : MarketingCampaign :=
  { id := { value := 9 }
    platform := AdPlatform.GoogleLike
    adType := AdType.Search
    destination := AdDestination.MarketplaceStore Marketplace.EtsyLike
    status := CampaignStatus.Active
    budget := 5000
    spend := 1200
    impressions := 1000
    clicks := 90
    conversions := 8
    attributedRevenue := 6000
    spend_le_budget := by norm_num
    clicks_le_impressions := by norm_num }

def marketingExamplesPass : Bool :=
  campaignsSpendTotal [marketingCampaignExample, marketingCampaignExample] == 2400 &&
    campaignsBudgetTotal [marketingCampaignExample, marketingCampaignExample] == 10000 &&
    attributionCreditTotal
      [{ campaignId := { value := 9 }, orderId := { value := 1 }, amount := 300 },
       { campaignId := { value := 10 }, orderId := { value := 1 }, amount := 450 }] == 750

example : destinationMatchesMarketplace marketingCampaignExample.destination Marketplace.EtsyLike := by
  simp [marketingCampaignExample, destinationMatchesMarketplace]

example : canSendMarketingMessage SubscriptionStatus.Subscribed := by
  exact subscribed_can_receive_marketing

example : ¬ canRetarget ConsentStatus.Denied := by
  exact denied_consent_cannot_retarget

/-- info: true -/
#guard_msgs in
#eval marketplaceExamplesPass

/-- info: true -/
#guard_msgs in
#eval marketingExamplesPass

end CommerceTheory.Tests
