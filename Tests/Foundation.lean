import CommerceTheory.Foundation

namespace CommerceTheory.Tests

def bp12_5 : BasisPoints :=
  { value := 1250
    value_le_10000 := by norm_num }

def roundDivExamplesPass : Bool :=
  roundDiv RoundingMode.Floor 105 10 == 10 &&
    roundDiv RoundingMode.Ceiling 101 10 == 11 &&
    roundDiv RoundingMode.Ceiling 100 10 == 10 &&
    roundDiv RoundingMode.HalfUp 105 10 == 11 &&
    roundDiv RoundingMode.HalfUp 104 10 == 10

def basisPointExamplesPass : Bool :=
  applyBps bp12_5 2000 == 250 &&
    roundBpsAmount RoundingMode.Floor 1999 bp12_5 == 249 &&
    roundBpsAmount RoundingMode.Ceiling 1999 bp12_5 == 250

def signedProfitLossExamplesPass : Bool :=
  profitAmount 850 1000 == 0 &&
    profitLossAmount 850 1000 == (-150 : Int) &&
    profitLossAmount 1350 1000 == (350 : Int)

/-- info: true -/
#guard_msgs in
#eval roundDivExamplesPass

/-- info: true -/
#guard_msgs in
#eval basisPointExamplesPass

/-- info: true -/
#guard_msgs in
#eval signedProfitLossExamplesPass

end CommerceTheory.Tests
