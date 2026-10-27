public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Field K]

theorem le_factorization_card_fixedSubgroup_E8_two (hK : Nat.card K = 2)
    {θ : MulAut (adjointGroup .E8 K)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    72 ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have : Finite (adjointGroup .E8 K) := by
    have : Finite (ModGL Tag.E8 K) := finite_modGL
    infer_instance
  obtain ⟨w, rfl⟩ := forall_mem_range_conj_E7_E8_two (Or.inr rfl) hK θ
  have hZ := center_adjointGroup_eq_bot_field .E8 K
  have hw2 : w * w = 1 := by
    have h1 : MulAut.conj (w * w) = 1 := by rw [map_mul]; exact hθ
    have hc : w * w ∈ center (adjointGroup .E8 K) := by
      rw [mem_center_iff]
      intro g
      have h2 : w * w * g * (w * w)⁻¹ = g := by
        have := congrArg (fun φ : MulAut (adjointGroup .E8 K) => φ g) h1
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * (w * w) = w * w * g * (w * w)⁻¹ * (w * w) := by rw [h2]
        _ = w * w * g := by group
    rw [hZ, mem_bot] at hc
    exact hc
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hθ1 (map_one _)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hdvd := two_pow_dvd_card_centralizer_E8 hK' hwo
  rw [mul_one] at hdvd
  change 72 ≤ (Nat.card (fixedSubgroup (MulAut.conj w))).factorization 2
  rw [fixedSubgroup_conj_eq_centralizer]
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd

end CFSG.SeitzReduction.E8Pilot
end
