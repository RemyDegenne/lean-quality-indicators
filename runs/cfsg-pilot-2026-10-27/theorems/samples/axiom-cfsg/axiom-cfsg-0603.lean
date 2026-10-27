public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

variable (c₀ : K) (hc₀ : c₀ ≠ 0) (Q : QuadraticForm K V) (ξ : V ≃ₗ[K] (Fin 4 → extension c₀))
  (hpol : ∀ v u, ξ u 2 = 0 → ξ u 3 = 0 → polar Q v u = (ξ v 0 * ξ u 1 + ξ u 0 * ξ v 1).re)
  (hQu : ∀ u, ξ u 2 = 0 → ξ u 3 = 0 → Q u = (ξ u 0 * ξ u 1).re)

include hQu hc₀ in
theorem Q_vw1 : Q (vw1 c₀ ξ) = 2 := by
  rw [hQu _ (by simp) (by simp)]
  simp only [LinearEquiv.apply_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    QuadraticAlgebra.re_mul]
  field_simp
  ring

end OIO
end CFSG.ComponentClassification.CatFactsL4U4
end
