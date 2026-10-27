public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem k18_B0_card (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(k18B0 t tau x₁ x₂ rho) = 2 ^ 6 := by
  rw [k18B0]
  set g : G := x₁ * x₂ with hgdef
  set Y : Subgroup G := ctxYq t tau x₁ x₂ rho with hYdef
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQdef
  have hYQ : Y ≤ Q := ctxYq_le_ctxQ
  have hgQ : g ∈ Q := by
    rw [hgdef, hQdef]
    exact hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hcardYsup : Nat.card ↥(Y ⊔ zpowers g) = 2 ^ 5 := by
    rw [hYdef, hgdef]
    exact k18_card_Y_sup hc
  have htau2 : tau ^ 2 = 1 := (ctx13_relations hc).2.2.2.1
  have htau_ne : tau ≠ 1 := by
    intro h
    exact (ctx13_relations hc).2.2.2.2.1 (by rw [h]; exact Subgroup.one_mem (zpowers t))
  have htaucard : Nat.card (zpowers tau) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime htau2 htau_ne]
  have htau_norm_Y : ∀ y ∈ Y, tau * y * tau⁻¹ ∈ Y := by
    intro y hy
    have hyQ : y ∈ Q := hYQ hy
    have h2 : y ^ 2 = 1 :=
      ((mem_ctxYq_iff hc.q_iso y).mp (show y ∈ ctxYq t tau x₁ x₂ rho from hy)).2
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h2)
    rw [hc.tau_inv_Q y hyQ, hyinv]
    exact hy
  have htau_norm_H : ∀ x ∈ Y ⊔ zpowers g, tau * x * tau⁻¹ ∈ Y ⊔ zpowers g := by
    have hHT : Y ≤ (Y ⊔ zpowers g).comap (MulAut.conj tau).toMonoidHom := by
      intro y hy
      rw [Subgroup.mem_comap]
      change tau * y * tau⁻¹ ∈ Y ⊔ zpowers g
      exact Subgroup.mem_sup_left (htau_norm_Y y hy)
    have hKT : zpowers g ≤ (Y ⊔ zpowers g).comap (MulAut.conj tau).toMonoidHom := by
      intro k hk
      rw [Subgroup.mem_comap]
      change tau * k * tau⁻¹ ∈ Y ⊔ zpowers g
      have htau_g : tau * g * tau⁻¹ = g⁻¹ := hc.tau_inv_Q g hgQ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [show tau * g ^ n * tau⁻¹ = (tau * g * tau⁻¹) ^ n by
        rw [← MulAut.conj_apply tau (g ^ n), map_zpow (MulAut.conj tau) g n,
          MulAut.conj_apply tau g]]
      rw [htau_g, inv_zpow']
      exact Subgroup.mem_sup_right
        (Subgroup.zpow_mem (zpowers g) (Subgroup.mem_zpowers g) (-n))
    intro x hx
    exact Subgroup.mem_comap.mp (sup_le hHT hKT hx)
  have hKnorm : ∀ k ∈ zpowers tau, ∀ h ∈ Y ⊔ zpowers g, k * h * k⁻¹ ∈ Y ⊔ zpowers g := by
    intro k hk h hh
    rcases k18k_zpowers_of_sq_one htau2 hk with hk1 | hktau
    · rw [hk1, one_mul, inv_one, mul_one]; exact hh
    · rw [hktau]; exact htau_norm_H h hh
  have hHleQ : Y ⊔ zpowers g ≤ Q := sup_le hYQ (Subgroup.zpowers_le_of_mem hgQ)
  have htau_notQ : tau ∉ Q := Ctx13.tau_not_mem_Q hc
  have hbotQ : zpowers tau ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxQ⟩ := Subgroup.mem_inf.mp hx
    rcases k18k_zpowers_of_sq_one htau2 hxt with h | h
    · rw [h]; exact Subgroup.mem_bot.mpr rfl
    · rw [h] at hxQ; exact absurd hxQ htau_notQ
  have hHK : (Y ⊔ zpowers g) ⊓ zpowers tau = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxQ : x ∈ Q := hHleQ hxH
    have : x ∈ zpowers tau ⊓ Q := ⟨hxt, hxQ⟩
    rwa [hbotQ] at this
  have hcl : closure ({g, tau} : Set G) = zpowers g ⊔ zpowers tau := by
    have hset : ({g, tau} : Set G) = ({g} : Set G) ∪ {tau} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure g,
      ← Subgroup.zpowers_eq_closure tau]
  have hB0 : Y ⊔ closure ({g, tau} : Set G) = (Y ⊔ zpowers g) ⊔ zpowers tau := by
    rw [hcl, sup_assoc]
  rw [hB0]
  rw [card_sup_eq_mul (H := Y ⊔ zpowers g) (K := zpowers tau) hKnorm hHK,
    hcardYsup, htaucard]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
end
