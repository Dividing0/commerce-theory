import CommerceTheory.OpportunityPortfolio
import Cslib.Algorithms.Lean.MergeSort.MergeSort

namespace CommerceTheory

/-! ## CSLib-backed dropship opportunity ranking -/

/-!
CSLib's timed merge sort is a good fit for ranking opportunity scores: it gives
both the sorted result and a comparison-count bound while preserving the input
keys as a permutation.
-/

/-- A sortable opportunity key: expected profit. -/
abbrev OpportunityRankKey := Money

/-- Convert a validated opportunity candidate into the key used by the ranking pass. -/
def opportunityRankKey (candidate : DropshipOpportunityCandidate) : OpportunityRankKey :=
  candidate.expectedProfit

/-- Extract sortable rank keys from a candidate list. -/
def opportunityRankKeys (candidates : List DropshipOpportunityCandidate) :
    List OpportunityRankKey :=
  candidates.map opportunityRankKey

/-- Rank opportunity keys from lowest expected profit to highest, counting comparisons. -/
def rankOpportunityKeys
    (candidates : List DropshipOpportunityCandidate) :
    Cslib.Algorithms.Lean.TimeM Nat (List OpportunityRankKey) :=
  Cslib.Algorithms.Lean.TimeM.mergeSort (opportunityRankKeys candidates)

/-- The ranking key's profit component preserves the candidate's minimum-profit floor. -/
theorem opportunityRankKey_profit_floor (candidate : DropshipOpportunityCandidate) :
    candidate.minProfit ≤ opportunityRankKey candidate := by
  exact candidate.expectedProfit_ge_minProfit

/-- CSLib merge sort returns rank keys in ascending order. -/
theorem rankOpportunityKeys_sorted
    (candidates : List DropshipOpportunityCandidate) :
    Cslib.Algorithms.Lean.TimeM.IsSorted (rankOpportunityKeys candidates).ret := by
  unfold rankOpportunityKeys
  exact Cslib.Algorithms.Lean.TimeM.mergeSort_sorted (opportunityRankKeys candidates)

/-- Ranking preserves exactly the same multiset of extracted opportunity keys. -/
theorem rankOpportunityKeys_perm
    (candidates : List DropshipOpportunityCandidate) :
    List.Perm (rankOpportunityKeys candidates).ret (opportunityRankKeys candidates) := by
  unfold rankOpportunityKeys
  exact Cslib.Algorithms.Lean.TimeM.mergeSort_perm (opportunityRankKeys candidates)

/-- Ranking cannot add or drop opportunity keys. -/
theorem rankOpportunityKeys_length
    (candidates : List DropshipOpportunityCandidate) :
    (rankOpportunityKeys candidates).ret.length = candidates.length := by
  unfold rankOpportunityKeys opportunityRankKeys
  rw [Cslib.Algorithms.Lean.TimeM.mergeSort_same_length]
  simp

/-- CSLib's comparison-count bound for the opportunity-ranking pass. -/
theorem rankOpportunityKeys_time
    (candidates : List DropshipOpportunityCandidate) :
    (rankOpportunityKeys candidates).time ≤
      candidates.length * Nat.clog 2 candidates.length := by
  unfold rankOpportunityKeys opportunityRankKeys
  simpa using
    Cslib.Algorithms.Lean.TimeM.mergeSort_time
      (List.map opportunityRankKey candidates)

end CommerceTheory
