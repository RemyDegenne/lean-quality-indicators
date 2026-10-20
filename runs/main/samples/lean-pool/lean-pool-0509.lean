@[expose] public section

open Finset

namespace KasamiCyclicAdditive.Phase

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

lemma weilSum_eq {ψ : AddChar K ℂ} {m D : ℕ} (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) {A B : K} (hA3 : A ^ 3 ≠ 1)
    {u v : K} (hu : u ∈ cubeRootsOne K) (hv : v ∈ cubeRootsOne K) :
    weilSum ψ D A B u v = (Fintype.card K : ℂ) * ((rootCount D A B u v : ℂ) - 1) := by
  rw [mem_cubeRootsOne] at hu hv
  -- on the slice `y = 0` the coefficient `u + v A^D` is nonzero, since `A^3 ≠ 1`
  have hAD : u + v * A ^ D ≠ 0 := by
    intro h
    rw [CharTwo.add_eq_zero] at h
    have h3 : (1 : K) = (A ^ 3) ^ D := by
      have h4 := congrArg (· ^ 3) h
      simp only [mul_pow, hu, hv, one_mul, ← pow_mul] at h4
      rw [h4]
      ring_nf
    exact hA3 (by rw [← pow_mul_eq_self hm hD hmD (A ^ 3), pow_mul', ← h3, one_pow])
  set C : K → K := fun t => u * t ^ D + v * (A * t + B) ^ D + 1 with hC
  -- for `y ≠ 0` substitute `x = t y`
  have hslice : ∀ y : K, y ≠ 0 →
      ∑ x : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D) = ∑ t : K, ψ (C t * y ^ D) := by
    intro y hy
    refine (Fintype.sum_bijective (fun t : K => t * y) (mulRight_bijective₀ y hy) _ _ ?_).symm
    intro t
    congr 1
    have h1 : A * (t * y) + B * y = (A * t + B) * y := by ring
    rw [hC]
    simp only [h1, mul_pow]
    ring
  -- the slice `y = 0` vanishes
  have hzero : ∑ x : K, ψ (u * x ^ D + v * (A * x + B * (0:K)) ^ D + (0:K) ^ D) = 0 := by
    have hrw : ∀ x : K, u * x ^ D + v * (A * x + B * (0:K)) ^ D + (0:K) ^ D
        = (u + v * A ^ D) * x ^ D := by
      intro x
      simp only [mul_zero, add_zero, zero_pow hD, mul_pow]
      ring
    simp only [hrw]
    rw [sum_psi_mul_powD hψ hm hD hmD, ite_eq_right hAD]
  have hswap : weilSum ψ D A B u v
      = ∑ y : K, ∑ x : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D) := by
    rw [weilSum, Finset.sum_comm]
  have hcompl : weilSum ψ D A B u v
      = ∑ y ∈ ({0} : Finset K)ᶜ, ∑ x : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D) := by
    rw [hswap, ← Finset.sum_add_sum_compl ({0} : Finset K), Finset.sum_singleton, hzero, zero_add]
  rw [hcompl, Finset.sum_congr rfl (fun y hy => hslice y (by simpa using hy)), Finset.sum_comm]
  have hinner : ∀ t : K, ∑ y ∈ ({0} : Finset K)ᶜ, ψ (C t * y ^ D)
      = (if C t = 0 then (Fintype.card K : ℂ) else 0) - 1 := by
    intro t
    have h := Finset.sum_add_sum_compl ({0} : Finset K) (fun y : K => ψ (C t * y ^ D))
    rw [sum_psi_mul_powD hψ hm hD hmD] at h
    simp only [Finset.sum_singleton, zero_pow hD, mul_zero, AddChar.map_zero_eq_one] at h
    linear_combination h
  rw [Finset.sum_congr rfl (fun t _ => hinner t), Finset.sum_sub_distrib]
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  have hR : (Finset.univ.filter (fun t : K => C t = 0)).card = rootCount D A B u v := by
    rw [rootCount]
    congr 1
    apply Finset.filter_congr
    intro t _
    rw [hC]
    simp [CharTwo.add_eq_zero]
  rw [hR]
  ring

end KasamiCyclicAdditive.Phase
end
