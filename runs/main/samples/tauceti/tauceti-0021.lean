public section

open Polynomial Equiv Equiv.Perm

namespace TauCeti

variable {F : Type*} [Field F] {f : F[X]}

variable {j : TransitiveGroupIndex 4}

variable (hchar : ringChar F ≠ 2) (hf : f.Monic)

include hchar hf in
theorem hasGaloisLabel_four_zero_or_two_iff_existsUnique_isRoot_resolvent :
    (HasGaloisLabel f (⟨0, by simp⟩ : TransitiveGroupIndex 4) ∨
        HasGaloisLabel f (⟨2, by simp⟩ : TransitiveGroupIndex 4)) ↔
      Irreducible f ∧ f.natDegree = 4 ∧
        ∃! a : F, (quarticD4Spec.specialize F f).IsRoot a := by
  constructor
  · intro h
    obtain ⟨hirr, hdeg, hsq, a, ha⟩ := (hasGaloisLabel_four_zero_or_two_iff hchar hf).1 h
    refine ⟨hirr, hdeg, a, ha, ?_⟩
    intro x hx
    by_contra hxa
    have hresdeg := natDegree_quarticD4Spec_specialize f
    have hsplit := Splits.of_natDegree_eq_three_of_isRoot_of_isRoot_of_ne hresdeg ha hx hxa
    apply hsq
    rw [discr_quarticD4Spec_specialize hf hdeg]
    exact (splits_iff_isSquare_discr_of_natDegree_eq_three_of_isRoot
      hresdeg hchar ha).1 hsplit
  · rintro ⟨hirr, hdeg, a, ha, huniq⟩
    have hsep := Polynomial.separable_of_irreducible_of_natDegree_eq_four hchar hirr hdeg
    have hressep := (separable_quarticD4Spec_specialize_iff hf hdeg).2 hsep
    have hresdeg := natDegree_quarticD4Spec_specialize f
    have hsq : ¬ IsSquare f.discr := by
      intro hsq
      have hressq : IsSquare (quarticD4Spec.specialize F f).discr := by
        rwa [← discr_quarticD4Spec_specialize hf hdeg]
      have hsplit :=
        (splits_iff_isSquare_discr_of_natDegree_eq_three_of_isRoot hresdeg hchar ha).2 hressq
      obtain ⟨x, hx, hxa⟩ := hsplit.exists_isRoot_ne hressep (by omega) a
      exact hxa (huniq x hx)
    apply (hasGaloisLabel_four_zero_or_two_iff hchar hf).2
    exact ⟨hirr, hdeg, hsq, a, ha⟩

end TauCeti
end
