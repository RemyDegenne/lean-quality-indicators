public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem exists_sigma_aut {σ : G} (hσ : H.IsSigma σ) (hσN : σ ∈ normalizer (S : Set G)) :
    ∃ φ : MulAut Λ, φ ^ 7 = 1 ∧ (∀ a : Λ, φ a = a → a = 1) ∧
      ∀ (i : ℕ) (a : Λ), ((φ ^ i) a : G) = σ ^ i * a * (σ ^ i)⁻¹ := by
  have hσΛ : σ ∈ normalizer (Λ : Set G) := h.N_le_normalizer_Λ hσN
  have hpow := J1Std.normalizerMonoidHom_pow_apply hσΛ
  obtain ⟨a, ha⟩ := hσ.exists_pow_eq_one
  have h7odd : Odd (7 ^ a) := Odd.pow (by decide)
  have hg7 : (σ ^ 7) ^ 7 ^ a = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
  have hcentr : ∀ l ∈ Λ, σ ^ 7 * l * (σ ^ 7)⁻¹ = l :=
    h.centralizes_Λ_of_odd_pow (pow_mem hσN 7) h7odd hg7 fun e he => hσ.pow_seven_apply_E he
  refine ⟨Λ.normalizerMonoidHom ⟨σ, hσΛ⟩, ?_, ?_, hpow⟩
  · refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hpow 7 b]
    exact hcentr b b.2
  · intro b hb
    by_contra hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h.pgroup ⟨b.1, h.le b.2⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hne (Subtype.ext (orderOf_eq_one_iff.1 hk))
    have hbΛ : b.1 ^ (2 ^ (k - 1)) ∈ Λ := Subgroup.pow_mem Λ b.2 _
    have hbsq : b.1 ^ (2 ^ (k - 1)) * b.1 ^ (2 ^ (k - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk1),
        ← hk]
      exact pow_orderOf_eq_one _
    have hb1 : b.1 ^ (2 ^ (k - 1)) ≠ 1 := by
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hk]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hσb : σ * b.1 ^ (2 ^ (k - 1)) * σ⁻¹ = b.1 ^ (2 ^ (k - 1)) := by
      have : σ * b.1 * σ⁻¹ = b.1 := congrArg Subtype.val hb
      rw [← conj_pow, this]
    exact hσ.free (h.mem_E_of_sq hbΛ hbsq) hb1 hσb

end Stage
end CFSG.EvenSporadicStandard.ReeStd
end
