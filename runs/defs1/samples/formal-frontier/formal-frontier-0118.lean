public section

open DirectSum

namespace GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (M : Submonoid A)

variable (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜)

/-- The degree-`i` part of a localized fraction.  A denominator degree is
chosen, and the numerator is projected to degree `i` plus that denominator
degree.  The localization relation makes the result independent of the
chosen representative, even when homogeneous denominators are zero divisors. -/
@[expose] noncomputable def projectionFun (i : ι) (x : Localization M) : Localization M :=
  x.liftOn
    (fun a s ↦ Localization.mk
      (DirectSum.decompose 𝒜 a (i + (hM s.2).choose) : A) s)
    fun {a₁ a₂} {s₁ s₂} h ↦ by
      rw [Localization.mk_eq_mk_iff]
      rw [Localization.r_iff_exists] at h ⊢
      obtain ⟨s, hs⟩ := h
      refine ⟨s, ?_⟩
      replace hs := congr((DirectSum.decompose 𝒜 $hs
        ((hM s.2).choose + ((hM s₂.2).choose +
          (i + (hM s₁.2).choose))) : A))
      simp_rw [DirectSum.decompose_mul,
        DirectSum.decompose_of_mem _ (hM (Subtype.prop _)).choose_spec,
        DirectSum.coe_of_mul_apply_add] at hs
      rw [show (hM s₂.2).choose + (i + (hM s₁.2).choose) =
        (hM s₁.2).choose + (i + (hM s₂.2).choose) by ac_rfl,
        DirectSum.coe_of_mul_apply_add] at hs
      exact hs

end GradedLocalization
end
