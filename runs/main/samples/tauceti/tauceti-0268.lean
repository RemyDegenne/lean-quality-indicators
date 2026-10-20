public section

namespace TauCeti

open freeProP Matrix

universe u

attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime]

section Presented

variable {X : Type u} {r : freeProP p X}

theorem HasPrescriptionProperty.range_le_unitsPrincipal_iff_forall_pow_dvd_exponentSum [Finite X]
    (hr : r ∈ proPFrattini p (freeProP p X))
    (hnd : (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate)
    {χ : presentedProP p X {r} →ₜ* ℤ_[p]ˣ} (hχ : HasPrescriptionProperty χ) (k : ℕ) :
    χ.toMonoidHom.range ≤ unitsPrincipal p k ↔
      ∀ x, (p : ℤ_[p]) ^ k ∣ (exponentSum p X r).toAdd x := by
  classical
  have := Fintype.ofFinite X
  -- Every continuous crossed homomorphism for the pulled-back character vanishes at `r`.
  have hkill : ∀ F : freeProP p X → ℤ_[p], Continuous F →
      IsCrossedHom (χ.comp (presentedProP.mk p {r})) F → F r = 0 := fun F hFc hF ↦
    (presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero
      (Set.singleton_subset_iff.2 hr) χ).1 hχ F hFc hF r rfl
  -- The values on the generators of the exponent sum at `j`.
  set c : X → X → ℤ_[p] := fun j x ↦ (exponentSum p X (of x)).toAdd j
  rw [range_le_unitsPrincipal_iff_forall_of]
  refine ⟨fun h j ↦ ?_, fun he ↦ ?_⟩
  · -- The exponent sum at `j` and the crossed homomorphism for `χ` with the same values on the
    -- generators are congruent modulo `p^k`, and the latter vanishes at `r`.
    have := IsCrossedHom.pow_dvd_sub_of_forall_of_eq (χ := 1)
      (χ' := χ.comp (presentedProP.mk p {r})) (k := k)
      (fun x ↦ by simpa [ContinuousMonoidHom.coe_one] using h x) (isCrossedHom_one_exponentSum j)
      (isCrossedHom_crossedHom _ (c j)) (continuous_exponentSum_apply j)
      (continuous_crossedHom _ (c j)) (fun x ↦ (crossedHom_of _ (c j) x).symm) r
    rwa [hkill _ (continuous_crossedHom _ (c j)) (isCrossedHom_crossedHom _ (c j)), zero_sub,
      dvd_neg] at this
  · induction k with
    | zero => simp
    | succ k ih =>
      exact pow_succ_dvd_sub_one_of_forall_pow_succ_dvd_exponentSum hr hnd hkill
        (ih fun x ↦ (pow_dvd_pow _ k.le_succ).trans (he x)) he

end Presented
end TauCeti
end
