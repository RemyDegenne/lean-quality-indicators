public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter

open CFSG.Blueprint

section CentB

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem z2BigModelCent_holds (r : ℕ) : Z2BigModelCent r := by
  intro hr X _ _ p f hL Q e
  obtain ⟨F, _, _, hF, h4, hp, E, hz⟩ :=
    exists_normalized_emb hL.simple hL.odd hL.even hL.model
      (quatInvolution_sq hr e) (quatInvolution_ne_one hr e)
      (quatInvolution_mem_fstar hL.index hr e)
  haveI : Fact p.Prime := ⟨hp⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hF h4
    omega
  obtain ⟨σ₀, hσ₀1, hσ₀2, hq⟩ := exists_frob_half hF hL.even hf0
  refine ⟨?_, ?_⟩
  · intro x hx hk
    exact cent_two_elements E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hx hk
  · intro H hH hHQ
    let θ : MulAut X →* (F ≃+* F) := SemidirectProduct.rightHom.comp E.ρ
    let ζ : MulAut X := MulAut.conj (quatInvolution r e)
    have hright : ∀ β : MulAut X, θ β = (E.ρ β).right := fun β => rfl
    have hub : ubar F = E.ρ ζ := by
      change ubar F = E.ρ (MulAut.conj (quatInvolution r e))
      rw [ubar_eq, ← inl_pD_eq, ← hz]
    have hζ2 : ζ * ζ = 1 := by
      change MulAut.conj (quatInvolution r e) * MulAut.conj (quatInvolution r e) = 1
      rw [← map_mul, quatInvolution_sq hr e, map_one]
    have hζ1 : ζ ≠ 1 := by
      intro h
      apply quatInvolution_ne_one hr e
      apply E.conjInj
      change MulAut.conj (quatInvolution r e) = MulAut.conj (1 : X)
      rw [show MulAut.conj (quatInvolution r e) = 1 from h, map_one]
    have hθ : ∀ β ∈ H, θ β = 1 ∨ θ β = σ₀ := by
      intro β hβ
      obtain ⟨k, hkord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨β, hβ⟩
      rw [Subgroup.orderOf_mk] at hkord
      have hk : β ^ 2 ^ k = 1 := by rw [← hkord]; exact pow_orderOf_eq_one β
      have hgr : (E.ρ β).right * (E.ρ β).right = 1 :=
        rho_fix_field_sq E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hL.arith
          (hHQ β hβ) hk
      rcases ringAut_sq_eq_one hF hL.odd h4 hσ₀1 hσ₀2 hgr with h | h
      · left; rw [hright β, h]
      · right; rw [hright β, h]
    have h1 : ∀ β ∈ H, θ β = 1 → β = 1 ∨ β = ζ := by
      intro β hβ hθβ
      obtain ⟨k, hkord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨β, hβ⟩
      rw [Subgroup.orderOf_mk] at hkord
      have hk : β ^ 2 ^ k = 1 := by rw [← hkord]; exact pow_orderOf_eq_one β
      have hgr : (E.ρ β).right * (E.ρ β).right = 1 :=
        rho_fix_field_sq E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hL.arith
          (hHQ β hβ) hk
      have hk' : (E.ρ β) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
      have htri := centralizer_qEmb E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq
        (fun c => rho_comm_qEmb E e (hHQ β hβ) c) hgr hk'
      rcases htri with h | h | h
      · left
        exact E.inj (by rw [h, map_one])
      · right
        exact E.inj (by rw [h, hub])
      · exfalso
        have h1r : (E.ρ β).right = 1 := by rw [← hright β, hθβ]
        exact hσ₀1 (h.1.symm.trans h1r)
    have h2 : ∀ β ∈ H, θ β ≠ 1 → β * β = ζ := by
      intro β hβ hθβ
      obtain ⟨k, hkord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨β, hβ⟩
      rw [Subgroup.orderOf_mk] at hkord
      have hk : β ^ 2 ^ k = 1 := by rw [← hkord]; exact pow_orderOf_eq_one β
      have hgr : (E.ρ β).right * (E.ρ β).right = 1 :=
        rho_fix_field_sq E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hL.arith
          (hHQ β hβ) hk
      have hk' : (E.ρ β) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
      have htri := centralizer_qEmb E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq
        (fun c => rho_comm_qEmb E e (hHQ β hβ) c) hgr hk'
      rcases htri with h | h | h
      · exfalso
        apply hθβ
        exact (hright β).trans (by rw [h]; rfl)
      · exfalso
        apply hθβ
        exact (hright β).trans (by rw [h, ubar_eq]; rfl)
      · have hEq : E.ρ (β * β) = E.ρ ζ := by
          rw [map_mul, h.2.1]
          exact hub
        exact E.inj hEq
    exact isCyclic_of_small θ σ₀ ζ hσ₀2 hζ2 hζ1 H hθ h1 h2

end CentB
end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
end
