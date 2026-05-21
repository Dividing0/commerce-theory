import CommerceTheory.Basic
import CommerceTheory.EventLanguage
import CommerceTheory.EventReplay
import CommerceTheory.ImplicitInvariants
import CommerceTheory.KeyedTotals
import CommerceTheory.Logistics
import CommerceTheory.OpportunityPortfolio
import CommerceTheory.OpportunityRanking
import CommerceTheory.Summary
import CommerceTheory.Workflow

namespace CommerceTheory.Tests

example :
    domainEventSymbols
      [ DomainEvent.OrderPlaced { value := 1 } 1000
      , DomainEvent.PaymentCaptured { value := 1 } 1000
      , DomainEvent.OrderShipped { value := 1 }
      ] =
    [ OrderEventSymbol.OrderPlaced
    , OrderEventSymbol.PaymentCaptured
    , OrderEventSymbol.OrderShipped
    ] := by
  rfl

def eventLanguageExamplesPass : Bool :=
  orderEventValidationStep
      OrderEventValidationState.Placed
      OrderEventSymbol.OrderShipped ==
    OrderEventValidationState.Invalid

def workflowExamplesPass : Bool :=
  paidFulfillmentTrace.length == 4 &&
    dropshipPODeliveryTrace.length == 4

example : (Cslib.Automata.Acceptor.language orderEventValidator).IsRegular := by
  exact orderEventValidator_language_regular

example :
    WebhookOrderingStep { lastSequence := 1 } { lastSequence := 3 } := by
  exact WebhookOrderingStep.accept { lastSequence := 1 } 3 (by norm_num)

example : production_order_pricing_safety = order_total_is_safe := by
  rfl

example :
    timed_allocation_total_safety = timedAllocationsTotal_le_availableTotal := by
  rfl

/-- info: true -/
#guard_msgs in
#eval eventLanguageExamplesPass

/-- info: true -/
#guard_msgs in
#eval workflowExamplesPass

end CommerceTheory.Tests
