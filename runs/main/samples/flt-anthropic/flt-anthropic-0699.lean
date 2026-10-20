namespace P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices

set_option maxHeartbeats 800000

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

open Finset BigOperators

namespace AnnulusG1

open ModularCurve ModularCurve.UVCrossingModel Finset

variable {W : Type*} [CommRing W]

theorem le_map_sum_add (v : AddValuation W ℕ∞) {ι : Type*} (s : Finset ι) (a : ι → W) (n w : ℕ∞)
    (h : ∀ k ∈ s, n ≤ v (a k) + w) : n ≤ v (∑ k ∈ s, a k) + w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      have h1 : n ≤ v (a x) + w := h x (Finset.mem_insert_self x s)
      have h2 : n ≤ v (∑ k ∈ s, a k) + w := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
      calc n ≤ min (v (a x)) (v (∑ k ∈ s, a k)) + w := by
            rw [← min_add_add_right]; exact le_min h1 h2
        _ ≤ v (a x + ∑ k ∈ s, a k) + w := add_le_add (v.map_add _ _) le_rfl

end AnnulusG1
end P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices
