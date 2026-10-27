public section

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.RankThree.OrthogonalInvolutions

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]

section Main

variable [FiniteDimensional (ZMod 2) Y] {Γ : Type*} [Group Γ] (ρ : Γ →* (Y ≃ₗ[ZMod 2] Y))

theorem finrank_commSpace_mul_ne_four {b : LinearMap.BilinForm (ZMod 2) Y}
    (hb : b.Nondegenerate)
    (hdiv : ∀ Z : Submodule (ZMod 2) Y, (∀ γ, ∀ z ∈ Z, ρ γ z ∈ Z) → 4 ∣ finrank (ZMod 2) Z)
    (hend : ∀ Z : Submodule (ZMod 2) Y, (∀ γ, ∀ z ∈ Z, ρ γ z ∈ Z) →
      finrank (ZMod 2) Z = 4 → ∀ φ : Y →ₗ[ZMod 2] Y, (∀ z ∈ Z, φ z ∈ Z) →
      (∀ γ, ∀ z ∈ Z, φ (ρ γ z) = ρ γ (φ z)) → ∃ c : ZMod 2, ∀ z ∈ Z, φ z = c • z)
    {u₁ u₂ u₃ : Y ≃ₗ[ZMod 2] Y} (hu₁ : ∀ y, u₁ (u₁ y) = y)
    (hi₁ : ∀ x y, b (u₁ x) (u₁ y) = b x y)
    (hi₂ : ∀ x y, b (u₂ x) (u₂ y) = b x y) (hg₁ : ∀ γ y, u₁ (ρ γ y) = ρ γ (u₁ y))
    (hg₂ : ∀ γ y, u₂ (ρ γ y) = ρ γ (u₂ y)) (h₁ : finrank (ZMod 2) (commSpace u₁) = 4)
    (h₂ : finrank (ZMod 2) (commSpace u₂) = 4) (hc' : ∀ y, u₁ (u₂ y) = u₂ (u₁ y))
    (h₃ : ∀ y, u₃ y = u₁ (u₂ y)) : finrank (ZMod 2) (commSpace u₃) ≠ 4 := by
  have e₃ : u₃ = u₁ * u₂ := LinearEquiv.ext fun y => by rw [h₃, LinearEquiv.mul_apply]
  have hc : u₁ * u₂ = u₂ * u₁ := LinearEquiv.ext fun y => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc']
  have hu₁' : u₁ * u₁ = 1 := LinearEquiv.ext fun y => by
    rw [LinearEquiv.mul_apply, hu₁]
    rfl
  rw [e₃]
  intro h
  by_cases he : commSpace u₁ = commSpace u₂
  · have e := eq_of_commSpace_eq ρ hb hend hi₁ hi₂ hg₁ hg₂ h₁ he
    rw [← e, hu₁'] at h
    have hbot : commSpace (1 : Y ≃ₗ[ZMod 2] Y) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨y, rfl⟩ := mem_commSpace.mp hz
      simp
    rw [hbot, finrank_bot] at h
    exact absurd h (by norm_num)
  have hinv := fun γ z (hz : z ∈ commSpace u₁ ⊓ commSpace u₂) =>
    (⟨commSpace_invariant ρ hg₁ γ z hz.1, commSpace_invariant ρ hg₂ γ z hz.2⟩ :
      ρ γ z ∈ commSpace u₁ ⊓ commSpace u₂)
  have h0 : commSpace u₁ ⊓ commSpace u₂ = ⊥ := by
    have hle : finrank (ZMod 2) ↥(commSpace u₁ ⊓ commSpace u₂) < 4 := by
      rcases (Submodule.finrank_mono (inf_le_left : commSpace u₁ ⊓ commSpace u₂ ≤ _)).lt_or_eq
        with hlt | heq
      · rwa [h₁] at hlt
      · exfalso
        have e1 := Submodule.eq_of_le_of_finrank_eq inf_le_left heq
        have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right :
          commSpace u₁ ⊓ commSpace u₂ ≤ commSpace u₂) (heq.trans (h₁.trans h₂.symm))
        exact he (e1.symm.trans e2)
    obtain ⟨k, hk⟩ := hdiv _ hinv
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hsum : ∀ y, (u₁ * u₂) y - y = (u₁ y - y) + (u₂ y - y) := by
    intro y
    have hm : u₁ (u₂ y - y) - (u₂ y - y) ∈ commSpace u₁ ⊓ commSpace u₂ := by
      refine ⟨sub_mem_commSpace u₁ _, ?_⟩
      have e : u₁ (u₂ y - y) - (u₂ y - y) = u₂ (u₁ y - y) - (u₁ y - y) := by
        have := congrArg (fun f : Y ≃ₗ[ZMod 2] Y => f y) hc
        simp only [LinearEquiv.mul_apply] at this
        rw [map_sub, map_sub, this]
        abel
      rw [e]
      exact sub_mem_commSpace u₂ _
    rw [h0, Submodule.mem_bot, map_sub] at hm
    rw [LinearEquiv.mul_apply]
    calc u₁ (u₂ y) - y = (u₁ (u₂ y) - u₁ y - (u₂ y - y)) + (u₁ y - y) + (u₂ y - y) := by abel
      _ = (u₁ y - y) + (u₂ y - y) := by rw [hm, zero_add]
  have hfix : fixSpace (u₁ * u₂) = b.orthogonal (commSpace u₁ ⊔ commSpace u₂) := by
    rw [orthogonal_sup_eq, ← fixSpace_eq_orthogonal hb hi₁, ← fixSpace_eq_orthogonal hb hi₂]
    ext y
    simp only [Submodule.mem_inf, mem_fixSpace]
    constructor
    · intro hy
      have e := hsum y
      rw [hy, sub_self, eq_comm, add_eq_zero_iff_eq_neg] at e
      have hm : u₁ y - y ∈ commSpace u₁ ⊓ commSpace u₂ := by
        refine ⟨sub_mem_commSpace u₁ y, ?_⟩
        rw [e]
        exact neg_mem (sub_mem_commSpace u₂ y)
      rw [h0, Submodule.mem_bot, sub_eq_zero] at hm
      refine ⟨hm, ?_⟩
      rw [hm, sub_self, eq_comm, neg_eq_zero, sub_eq_zero] at e
      exact e
    · rintro ⟨h1, h2⟩
      rw [LinearEquiv.mul_apply, h2, h1]
  have hdimsup : finrank (ZMod 2) ↥(commSpace u₁ ⊔ commSpace u₂) = 8 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (commSpace u₁) (commSpace u₂)
    rw [h0, finrank_bot, h₁, h₂] at this
    omega
  have e1 := finrank_commSpace_add_finrank_fixSpace (u₁ * u₂)
  have e2 := LinearMap.BilinForm.finrank_orthogonal hb (commSpace u₁ ⊔ commSpace u₂)
  rw [hfix] at e1
  have e3 : 8 ≤ finrank (ZMod 2) Y := hdimsup ▸ Submodule.finrank_le _
  omega

end Main
end CFSG.LargeExtraspecial.S9
end
