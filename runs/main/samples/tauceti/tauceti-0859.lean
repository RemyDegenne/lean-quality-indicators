public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

lemma wangδ_def (n : ℕ) :
    wangδ φ R n = (cyclicCoverShortComplex_shortExact φ R).δ (n + 1) n (by simp) ≫
      homologyMap (((singularChainComplexFunctor A).obj R).map
        (TopCat.ofHom (cylinderHomotopyEquiv F).toFun)) n := by
  rw [wangδ, cylinderHomologyIso_hom]

end TauCeti.MappingTorus
end
end
