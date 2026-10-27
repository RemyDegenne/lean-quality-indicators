public section

namespace CFSG.Quasithin.B45Exc

open Matrix Module CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover

section Offender

variable {p : ℕ} [hpf : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

theorem p2_internal_offender2F (hp11 : 11 ≤ p) [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {B : Subgroup (projectiveSL 2 (ZMod p))} (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      2 * Nat.log 2 (Nat.card B)) : False := by
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_two).1 h')
  have h4 : Nat.card B ≤ 4 := (p2_involution_structure hp5).2 B hBc hB2
  obtain ⟨⟨a, haB⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have ha1 : a ≠ 1 := fun h => ha (Subtype.ext h)
  by_cases hsmall : Nat.card B ≤ 2
  · have hlog : 2 * Nat.log 2 (Nat.card B) ≤ 2 :=
      Nat.mul_le_mul_left 2 ((Nat.log_mono_right hsmall).trans (by decide : Nat.log 2 2 ≤ 1))
    have hrk := finrank_range_disp_le_of_offender ρ haB (hoff.trans hlog)
    have := (p2_actor_of_low_rank_involution hp5 ρ hE ha1 (hB2 a haB) hrk).2.2
    omega
  have hlog : 2 * Nat.log 2 (Nat.card B) ≤ 4 :=
    Nat.mul_le_mul_left 2 ((Nat.log_mono_right h4).trans (by decide : Nat.log 2 4 ≤ 2))
  have hrkB : ∀ b ∈ B, finrank (ZMod 2) (LinearMap.range (disp ρ b)) ≤ 4 :=
    fun b hb => finrank_range_disp_le_of_offender ρ hb (hoff.trans hlog)
  have hp := p2_eleven_or_seventeen hp11 ρ hE ha1 (hB2 a haB) (hrkB a haB)
  have hge := p2_rank_ge_four hp ρ hE ha1 (hB2 a haB)
  have hfix := fixedSub_eq_ker_disp ρ haB (hoff.trans (hlog.trans hge))
  obtain ⟨t, htB, u, huB, ht1, hu1, htu⟩ := exists_two_ne_one hsmall
  obtain ⟨v, hvB, hv1, hva⟩ : ∃ v ∈ B, v ≠ 1 ∧ v ≠ a := by
    by_cases hta : t = a
    · exact ⟨u, huB, hu1, fun h => htu (hta.trans h.symm)⟩
    · exact ⟨t, htB, ht1, hta⟩
  have hker : LinearMap.ker (disp ρ a) ≤ LinearMap.ker (disp ρ v) := by
    rw [← hfix]
    exact fixedSub_le_ker_disp ρ hvB
  have hE' : QuasithinUnique.Setup.Family.commSub (ρ.comp (MonoidHom.id _)) ⊤ = ⊤ := by rw [MonoidHom.comp_id]; exact hE
  refine p2_contra_core hp11 (MonoidHom.id _) ρ hE' ?_ ha1 (hB2 a haB) (hrkB a haB)
    (hB2 v hvB) hv1 hva (hBc v hvB a haB) hker
  intro w hw2 hw1 hwa hwc c d hcd
  exact p2_conj_rotation h2 hw2 hw1 hwa hwc hcd

end Offender
end CFSG.Quasithin.B45Exc
end
