public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix

open CFSG.SectionRank.OddCover (u3Mat)

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Finite

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 3] (hF : Nat.card F = (3 ^ f) ^ 2)

include hF

theorem eq_bot_of_le_normalizer_lineU {a₀ : F} (ha₀ : a₀ ≠ 0)
    {W : Subgroup (SU (unitaryInvolution F 3 f) 3)} (hW3 : ¬ 3 ∣ Nat.card W)
    (hRW : lineU (unitaryInvolution_involutive hF) a₀ ≤
      Subgroup.normalizer (W : Set (SU (unitaryInvolution F 3 f) 3))) : W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (SU (unitaryInvolution F 3 f) 3) := Finite.of_injective _ Subtype.val_injective
  have hcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  have hW1 : ∀ w ∈ W, w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have hd1 : orderOf (⟨w, hw⟩ : W) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hw3, Subgroup.coe_one])
    have h1 : orderOf (⟨w, hw⟩ : W) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 (orderOf_dvd_natCard _)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have hf : f ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  have h9 : 3 ^ 2 ≤ Nat.card (lineU (unitaryInvolution_involutive hF) a₀) := by
    refine le_trans ?_ (card_lineU_ge hF ha₀)
    exact Nat.pow_le_pow_left (Nat.le_self_pow hf 3) 2
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three (isElemAbelian_lineU a₀) h9 hRW
    hcop fun v hvR hv1 => ?_
  rintro w ⟨hwW, hwv⟩
  have hwv' : w * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwv
  have hcomm : ∀ r ∈ lineU (unitaryInvolution_involutive hF) a₀, w * r = r * w := by
    intro r hr
    have h3 := commutator_pow_three_heisU hvR.1 hv1 hwv' hr.1
    have hW' : r * w * r⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRW hr) w).mp hwW) (W.inv_mem hwW)
    have h1 := hW1 _ hW' h3
    have key : w * r = (r * w * r⁻¹ * w⁻¹)⁻¹ * (r * w) := by group
    rw [key, h1, inv_one, one_mul]
  exact Subgroup.mem_bot.mpr (hW1 w hwW (pow_three_eq_one_of_forall_commute_lineU hF ha₀ hcomm))

end Finite
end CFSG.RankThree.PartTwo.Sec4.Item434CharThree
end
