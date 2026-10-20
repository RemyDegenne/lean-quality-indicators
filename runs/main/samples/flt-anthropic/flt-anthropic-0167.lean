namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

noncomputable section

namespace R4ODGlue

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable {q : ℕ} [Fact q.Prime]

section square

variable {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
  (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
  (hcomm : q'.comp p' = q''.comp p'')
  (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')

include hcomm hpb in
theorem eq_of_proj_eq {b₁ b₂ : B} (h' : p' b₁ = p' b₂) (h'' : p'' b₁ = p'' b₂) : b₁ = b₂ := by
  have hc : q' (p' b₁) = q'' (p'' b₁) := by
    have := congrArg (fun g => g b₁) hcomm
    simpa using this
  obtain ⟨b, -, huniq⟩ := hpb (p' b₁) (p'' b₁) hc
  exact (huniq b₁ ⟨rfl, rfl⟩).trans (huniq b₂ ⟨h'.symm, h''.symm⟩).symm

end square
end R4ODGlue
end
end P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
