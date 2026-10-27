public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three

open scoped Pointwise

section Split

theorem d4_sep (α β : Fin Tag.D4.rank → ℤ) (hα : IsRoot Tag.D4 α)
    (hβ : IsRoot Tag.D4 β)
    (h : ∀ j, (∑ k, Tag.D4.cartan j k * α k) % 3 = (∑ k, Tag.D4.cartan j k * β k) % 3) : α = β := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hα
  obtain ⟨m', rfl⟩ := CFSG.RankThree.Chevalley.isRoot_iff_exists_d4RootVec.1 hβ
  rw [d4_sep_check m m' h]

end Split
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f
end
