@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory

open scoped ContDiff Topology BigOperators

namespace NavierStokes.SlowStressSupport

theorem axial_stress_support {S : Set ℝ} (hS : IsOpen S) {n : ℕ} (hn : 0 < n)
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ n → exterior B S (v j)) (hU : ∀ j, j ≤ n → exterior B S (u j))
    (hP : exterior B S p) (haxis : ∀ eta ∈ S, ∀ j, j ≤ n → v j (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hprev : ∀ eta ∈ S, moment B 1 (u (n - 1)) eta = 0)
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ n →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, axialWeighted h n v u p (R, eta) = 0) :
    Smooth S (axialStress h n v u p) ∧ radialSupport S a B (axialStress h n v u p) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r * axialStress h n v u p (r, eta))
        (-axialWeighted h n v u p (R, eta)) R := by
  have hprev_le : n - 1 ≤ n := (Nat.sub_lt hn (by decide : 0 < 1)).le
  have hsm := smooth_axialDensity hS hv hu hp h hell
  have hax : ∀ eta ∈ S, conv n v u (0, eta) = 0 := by
    intro eta heta
    unfold conv
    apply Finset.sum_eq_zero
    intro j hj
    rw [haxis eta heta j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), zero_mul]
  have hfB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0 := by
    intro eta heta
    rw [exterior_conv_left hU eta heta B le_rfl, hP eta heta B le_rfl, add_zero]
  have htotal : ∀ eta ∈ S, moment B 0 (axialDensity h n v u p) eta = 0 :=
    fun eta heta => axial_integral_zero hS hv hu hp h B hell (hU n le_rfl) hV hax hum hflux hfB
      (hU (n - 1) hprev_le) hprev heta
  have hout := exterior_axialDensity hS hv hu hp h B hV hU hP
    (exterior_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) (hU (n - 1) (Nat.sub_le _ _)) h _ hell)
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, axialDensity h n v u p (R, eta) = 0 := by
    intro eta heta R hR
    rw [← axialWeighted_eq_density hS hv hu hp h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 1 ha hin, stress_radialSupport 1 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [axialWeighted_eq_density hS hv hu hp h heta (hdiv _ heta)]
  unfold axialStress
  simpa only [pow_one] using stress_weighted_hasDerivAt hS hsm 1 hR heta

end NavierStokes.SlowStressSupport
end
end
