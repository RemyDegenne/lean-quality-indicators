public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section E6Main

open CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

local instance e6NeZeroRank'' : NeZero Tag.E6.rank := ⟨by decide⟩

theorem rootChar_neg' {τ : Tag} {K : Type} [Field K] (v : Fin τ.rank → Kˣ) (x : Fin τ.rank → ℤ) :
    rootChar v (-x) = (rootChar v x)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

end E6Main
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f
end
