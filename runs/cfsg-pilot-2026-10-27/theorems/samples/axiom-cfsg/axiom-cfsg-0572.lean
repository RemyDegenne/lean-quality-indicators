public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ8

variable {K : Type} [Field K]

section Cartan

variable {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}

theorem fixCols_3_6 : FixCols (nd 3) 6 (by decide) := by unfold FixCols; decide +kernel

end Cartan
end CFSG.HardMathSupport.Seitz.TrialityOdd
end
