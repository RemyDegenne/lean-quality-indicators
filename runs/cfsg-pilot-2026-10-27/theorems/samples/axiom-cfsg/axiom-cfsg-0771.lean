public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

theorem conj_of_odd_mul {G : Type*} [Group G] {e t : G} (he : e * e = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (e * t))) : ∃ m : G, m * e * m⁻¹ = t := by
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set a := e * t with ha
  have hainv : a⁻¹ = t * e := by rw [ha, mul_inv_rev, he', ht']
  obtain ⟨j, hj⟩ := hodd
  have hea : e * a⁻¹ * e = a := by
    rw [hainv, ha]
    calc e * (t * e) * e = (e * t) * (e * e) := by group
      _ = e * t := by rw [he, mul_one]
  have hpow : ∀ k : ℕ, e * (a⁻¹ ^ k) * e = a ^ k := by
    intro k
    have : e * (a⁻¹ ^ k) * e⁻¹ = (e * a⁻¹ * e⁻¹) ^ k := by
      rw [← conj_pow]
    rw [he'] at this
    rw [this, hea]
  have hn : a ^ (2 * j + 1) = 1 := by
    rw [← hj]; exact pow_orderOf_eq_one a
  have hn' : a⁻¹ ^ (2 * j + 1) = 1 := by rw [inv_pow, hn, inv_one]
  set m := a⁻¹ ^ (j + 1) with hm
  refine ⟨m, ?_⟩
  have h2 : e * m⁻¹ * e = m := by
    have := hpow (j + 1)
    calc e * m⁻¹ * e = e⁻¹ * m⁻¹ * e⁻¹ := by rw [he']
      _ = (e * m * e)⁻¹ := by group
      _ = (a ^ (j + 1))⁻¹ := by rw [hm, this]
      _ = m := by rw [hm, inv_pow]
  have h1 : m * e * m⁻¹ = m * (e * m⁻¹ * e) * e⁻¹ := by group
  rw [h1, h2, he']
  have h3 : m * m = a⁻¹ := by
    rw [hm, ← pow_add]
    calc a⁻¹ ^ (j + 1 + (j + 1)) = a⁻¹ ^ (2 * j + 1) * a⁻¹ := by
          rw [← pow_succ]; congr 1; omega
      _ = a⁻¹ := by rw [hn', one_mul]
  rw [h3, hainv]
  calc t * e * e = t * (e * e) := by group
    _ = t := by rw [he, mul_one]

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
end
