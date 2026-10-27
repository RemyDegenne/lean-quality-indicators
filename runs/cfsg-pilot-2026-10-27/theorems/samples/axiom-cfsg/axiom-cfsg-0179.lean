public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ7

open scoped commutatorElement

variable {K : Type} [Field K]

section Collection

theorem xd_mergeO' (p : ℕ) (c d : K) : xd p c * xd p d = xd p (c + d) := (xd_add p c d).symm

end Collection
end CFSG.HardMathSupport.Seitz.TrialityOdd
end
