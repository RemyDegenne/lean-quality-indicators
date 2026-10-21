namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace

open Norming Singular Set

open scoped Classical Topology

lemma exists_initial_reduction (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) :
    ∃ (γ : Cut) (H : Submodule ℝ E), IsClosed (H : Set E) ∧
      ¬ FiniteDimensional ℝ H ∧
      (∀ a : Γ, (a : Cut) < γ → ∃ b : Γ, a < b ∧ (b : Cut) < γ) ∧
      (∀ β < γ, StrictlySingular ((initialP β).comp H.subtypeL)) ∧
      ∃ U : H →L[ℝ] F, ∀ x : H, initialP γ (U x) = x := by
  let : CompleteSpace F := hF.completeSpace_coe
  obtain ⟨γ,hγ,hsmall,hlim⟩ := exists_minimal_cut F hF hI
  obtain ⟨H,hH,hHi,U,hU⟩ := exists_lift_of_not_strictlySingular
    ((initialP γ).comp F.subtypeL) hγ
  let : CompleteSpace H := hH.completeSpace_coe
  refine ⟨γ,H,hH,hHi,hlim,?_,U,hU⟩
  intro β hβ
  have hh := (hsmall β hβ).comp_right _ U
  have he : ((initialP β).comp F.subtypeL).comp U = (initialP β).comp H.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    have hu : initialP γ ((U x : F) : E) = x := hU x
    change initialP β ((U x : F) : E) = initialP β (x : E)
    rw [← hu,initialP_initialP hβ.le]
  rwa [he] at hh

end SeparableQuotient.ActualSpace
end
end OAI
