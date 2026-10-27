public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

namespace ConnCex

variable (hC : ConnCex D)

include hC

theorem exists_thirdKind {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : Commute a b)
    (hnD : a * b ∉ D) :
    ∃ x ∈ D, ¬ Reach D a x ∧ ∃ n : ℕ, Odd n ∧ orderOf (x * (a * b)) = 2 * n := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hclass := hC.isClass
  by_contra hno
  push Not at hno
  have hu2 := hC.mul_mul_self_of_commute ha hb hc
  have hu1 := hC.mul_ne_one_of_ne hb hab
  have hker : a * b ∈ ker hN := by
    rw [mem_ker_iff]
    intro y hy
    by_cases hay : Reach D a y
    · have h1 := reach_conj hN (a * b) hay
      have hua : a * b * a * (a * b)⁻¹ = a := by
        rw [((Commute.refl a).mul_left hc.symm).eq, mul_inv_cancel_right]
      rw [hua] at h1
      exact reach_trans (reach_symm hay) h1
    · have hyD' : a * b * y * (a * b)⁻¹ ∈ D := hN _ y hy
      have hsq : y * (a * b * y * (a * b)⁻¹) = (y * (a * b)) ^ 2 := by
        rw [inv_eq_of_mul_eq_one_right hu2, pow_two]
        group
      rcases Nat.even_or_odd (orderOf (y * (a * b))) with ⟨m, hm⟩ | hodd
      · have hm0 : 0 < orderOf (y * (a * b)) := orderOf_pos _
        have hord2 : orderOf ((y * (a * b)) ^ 2) = m := by
          rw [orderOf_pow' _ two_ne_zero, hm, Nat.gcd_eq_right ⟨m, by ring⟩]
          omega
        have hmeven : ¬ Odd m := fun hmo => hno y hy hay m hmo (by omega)
        apply hC.reach_of_orderOf_dvd_four hy hyD'
        rw [hsq, hord2]
        have hroot := hD.orderOf_mul hy hyD'
        rw [hsq, hord2] at hroot
        rcases hroot with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h hmeven
      · exact absurd (mem_of_odd_orderOf_mul hclass hD hy hu2 hodd) hnD
  rw [hC.faith, Subgroup.mem_bot] at hker
  exact hu1 hker

end ConnCex
end CFSG.Timmesfeld.Bridge
end
