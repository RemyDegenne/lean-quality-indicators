public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

section Assembly

theorem centShapeSplit_Suz : CentShapeSplit 3 (NativeSporadic.Carrier .Suz) := by
  have e : NativeSporadic.Suz ≃* ↥suzM := suzEquivM
  haveI : Finite (NativeSporadic.Carrier .Suz) := Finite.of_equiv ↥suzM e.symm.toEquiv
  exact CentShapeSplit.of_equiv Nat.prime_three e.symm centShapeSplit_suzM

end Assembly
end CFSG.HardMathSupport.Dickson.I271
end
