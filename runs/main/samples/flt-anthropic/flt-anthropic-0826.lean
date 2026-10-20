namespace P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

noncomputable section

universe u

open PowerSeries MvFormalGroup MvFormalGroup.ArtinHasse

namespace CartierExistenceIntSol

variable (p : ℕ) [hp : Fact p.Prime]

scoped instance (k : ℕ) : Decidable (IsPPow p k) := by unfold IsPPow; infer_instance

section Descent

theorem incl_injective : Function.Injective (incl p) := by
  intro P Q h
  rw [incl_apply, incl_apply] at h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) h

end Descent
end CartierExistenceIntSol
end
end P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
