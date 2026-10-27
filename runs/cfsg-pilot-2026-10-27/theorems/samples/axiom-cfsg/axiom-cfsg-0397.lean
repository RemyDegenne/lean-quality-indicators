public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
  (d : Data G h)

theorem elemAbMod_A₁_sup_A₂ : ElemAbMod d.A₁ (d.A₁ ⊔ d.A₂) := by
  rw [d.A₁_sup_A₂]
  exact d.elemAbMod_pull (by rw [Vsub_sup_A₂sub_eq]; exact elemAbMod_Vsub_sB₂)

end Data
end CFSG.LocalAnalysis.EvenBN.U5
end
