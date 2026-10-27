public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {g : G}

theorem GElt.exists_frame_at_d_eq (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1)
    (hg : GElt z ι g) (hg1 : g * g = 1) :
    ∃ ιd : Perm (Fin 10) →* G, CentData (ι (swap 0 1)) ιd ∧ ιd (swap 0 1) = z ∧
      (∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 → ιd σ = ι σ) ∧
      g = ιd (swap 0 8 * swap 1 9) := by
  have hSig : ∀ ρ : Perm (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g :=
    (GElt.pairOrder_eq_N10_one_iff hC hg).1 hp
  obtain ⟨κ₀, hκ₀, hκ₀τ, hκ₀lift, -⟩ := exists_frame_at_conj hC hx hP2 cD₀
  obtain ⟨κ₁, hκ₁, hκ₁τ, hκ₁lift, -⟩ := exists_frame_at_conj hC hx hP2 cD₁
  rw [cD₀_conj_τ₀] at hκ₀
  rw [cD₁_conj_τ₀] at hκ₁
  have hκ₀lift' : ∀ ρ : Perm (Fin 8), κ₀ (liftS8 ρ) = ι (cD₀ * liftS8 ρ * cD₀⁻¹) := hκ₀lift hp
  have hκ₁lift' : ∀ ρ : Perm (Fin 8), κ₁ (liftS8 ρ) = ι (cD₁ * liftS8 ρ * cD₁⁻¹) := hκ₁lift hp
  have hκ₀swap : κ₀ (swap 0 1) = ι τ₀ := by
    have h := hκ₀lift' (swap (0 : Fin 8) 1)
    rwa [liftS8_swap01, cD₀_conj_swap] at h
  have hκ₀s23 : κ₀ (swap 2 3) = ι (swap 2 3) := by
    have h := hκ₀lift' (swap (2 : Fin 8) 3)
    rw [liftS8_swap23] at h
    rw [show cD₀ * swap (2 : Fin 10) 3 * cD₀⁻¹ = swap (2 : Fin 10) 3 by decide] at h
    exact h
  have hκ₁swap01 : κ₁ (swap 0 1) = ι (swap 0 1) := by
    have h := hκ₁lift' (swap (0 : Fin 8) 1)
    rw [liftS8_swap01] at h
    rw [show cD₁ * swap (0 : Fin 10) 1 * cD₁⁻¹ = swap (0 : Fin 10) 1 by decide] at h
    exact h
  have hκ₁swap23 : κ₁ (swap 2 3) = ι τ₀ := by
    have h := hκ₁lift' (swap (2 : Fin 8) 3)
    rw [liftS8_swap23] at h
    rw [show cD₁ * swap (2 : Fin 10) 3 * cD₁⁻¹ = τ₀ by decide] at h
    exact h
  have hlift₀ : ∀ ρ : Perm (Fin 8), ρ 0 = 0 → ρ 1 = 1 → κ₀ (liftS8 ρ) = ι (liftS8 ρ) := by
    intro ρ h0 h1
    rw [hκ₀lift' ρ, ← frameConj_apply ι cD₀ (liftS8 ρ),
      frameConj_cD₀_liftS8_of_fixed ι h0 h1]
  have hlift₁ : ∀ ρ : Perm (Fin 8), ρ 2 = 2 → ρ 3 = 3 → κ₁ (liftS8 ρ) = ι (liftS8 ρ) := by
    intro ρ h2 h3
    rw [hκ₁lift' ρ, ← frameConj_apply ι cD₁ (liftS8 ρ),
      frameConj_cD₁_liftS8_of_fixed ι h2 h3]
  have hgd₀ : g * ι (swap 0 1) = ι (swap 0 1) * g := by
    simpa only [liftS8_swap01] using hSig (swap (0 : Fin 8) 1)
  have hgd₁ : g * ι (swap 2 3) = ι (swap 2 3) * g := by
    simpa only [liftS8_swap23] using hSig (swap (2 : Fin 8) 3)
  obtain ⟨π₀, ε₀, hε₀, hgπ₀, hπ₀sq, hπ₀comm, hπ₀τ, hπ₀s⟩ :=
    pi_data hC hg hg1 hκ₀ hgd₀ hSig hκ₀τ hκ₀swap (fun ρ => ρ 0 = 0 ∧ ρ 1 = 1)
      (fun ρ hP => hlift₀ ρ hP.1 hP.2)
  obtain ⟨π₁, ε₁, hε₁, hgπ₁, hπ₁sq, hπ₁comm, hπ₁τ, hπ₁s⟩ :=
    pi_data hC hg hg1 hκ₁ hgd₁ hSig hκ₁τ hκ₁swap23 (fun ρ => ρ 2 = 2 ∧ ρ 3 = 3)
      (fun ρ hP => hlift₁ ρ hP.1 hP.2)
  have hπ₀cls : π₀ = cD₀ ∨ π₀ = swap 0 9 * swap 1 8 :=
    eq_cD₀_or_of_commutes π₀ hπ₀sq (fun ρ h0 h1 => hπ₀comm ρ ⟨h0, h1⟩) hπ₀τ hπ₀s
  have hπ₁cls : π₁ = cD₁ ∨ π₁ = swap 2 9 * swap 3 8 :=
    eq_cD₁_or_of_commutes π₁ hπ₁sq (fun ρ h2 h3 => hπ₁comm ρ ⟨h2, h3⟩) hπ₁τ hπ₁s
  have hπ₀23 : π₀ 2 = 2 ∧ π₀ 3 = 3 := by
    refine ⟨?_, ?_⟩ <;> rcases hπ₀cls with h | h <;> rw [h] <;> decide
  have hπ₁fac : ∃ t₁ t₂ ρ : Perm (Fin 10), π₁ = t₁ * t₂ ∧ ρ * t₁ * ρ⁻¹ = t₂ ∧
      t₁ 0 = 0 ∧ t₁ 1 = 1 ∧ t₂ 0 = 0 ∧ t₂ 1 = 1 ∧ ρ 0 = 0 ∧ ρ 1 = 1 :=
    exists_double_transposition_factors π₁ hπ₁cls
  have hε₀eq : ε₀ = 1 :=
    eq_one_of_two_frames hκ₀ hκ₁ hκ₁swap01 hκ₀s23 hπ₀23 hπ₁fac hε₀ hε₁ (by rw [← hgπ₀, hgπ₁])
  have hg_eq : g = κ₀ π₀ := by rw [hgπ₀, hε₀eq, one_mul]
  obtain ⟨ιd, hCd, hd, hagree, hgeq⟩ := frame_d_of_pi hκ₀ hκ₀lift' hκ₀τ hπ₀cls hg_eq
  exact ⟨ιd, hCd, hd, hagree, hgeq⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
end
