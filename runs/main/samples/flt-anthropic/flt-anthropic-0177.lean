namespace P2MW.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents

open scoped TensorProduct

open TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GrassPluckerEmb

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)

variable {R M k}

section glue

variable (D : Rep R M k) {n : ℕ} (g : Fin (n + 1) → M) (hg : Submodule.span R (Set.range g) = ⊤)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (mm k n + 1)) R

local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule (Fin (mm k n + 1)) R)

include hg in

theorem ψ_surjective (l : Fin (mm k n + 1)) : Function.Surjective (ψ D g l) := by
  haveI : IsOpenImmersion (D.pt (S D (τ g l)) (NS D (τ g l))).1 := by rw [pt_NS]; infer_instance
  have hgen := Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq R M k D.Gr D.p D.pt D.hpt
    D.V D.hVchart (Fin (n + 1)) g hg (τ g l) (S D (τ g l)) (NS D (τ g l))
    (TopologicalSpace.Opens.ext (by
      change Set.range ((D.pt (S D (τ g l)) (NS D (τ g l))).1).base = _
      rw [pt_NS, range_gS]))
  rw [← AlgHom.range_eq_top, eq_top_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro s ⟨a', c, i, hc, rfl⟩
  refine ⟨ProjSpace.ratio R (mm k n) l ((ε k n).symm (Function.update (ε k n l) i a')), ?_⟩
  change ψ D g l _ = c i
  rw [ψ_ratio]
  unfold a
  rw [← update_τ]
  exact (eq_Pl_update (τ g l) (Nτ D g l) (g a') c hc i).symm

end glue
end GrassPluckerEmb
end P2MW.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents
