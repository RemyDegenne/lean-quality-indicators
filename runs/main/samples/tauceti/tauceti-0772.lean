public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

@[reassoc (attr := simp)]
theorem wangInclusion_comp_wangConnecting (n : ℕ) :
    wangInclusion φ R (n + 1) ≫ wangConnecting φ R n = 0 := by
  rw [wangInclusion_eq]
  exact (Category.assoc _ _ _).trans
    ((congrArg _ (map_comp_wangConnecting φ R n)).trans comp_zero)

end TauCeti.MappingTorus
end
end
