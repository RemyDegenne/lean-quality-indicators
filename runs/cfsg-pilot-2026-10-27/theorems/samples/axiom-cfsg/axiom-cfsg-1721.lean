public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RootStandard

open Subgroup Matrix

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis GomiFusion FullCenterTorus

open scoped commutatorElement

variable {K : Type} [Field K]

variable [CharP K 2]

theorem commutatorElement_mul_left_of_comm {Y : Type*} [Group Y] {C : Subgroup Y} {z a b : Y}
    (hz : ∀ c ∈ C, z * c = c * z) (ha : a ∈ C) (hb : b ∈ C) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h1 := hz _ (mul_mem (mul_mem ha hb) (inv_mem ha))
  rw [commutatorElement_def, commutatorElement_def,
    show z * a * b * (z * a)⁻¹ * b⁻¹ = (z * (a * b * a⁻¹)) * z⁻¹ * b⁻¹ by group, h1]
  group

end RootStandard
end CFSG.LocalAnalysis.SymplecticFourStandard
end
