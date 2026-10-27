public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

section Native

variable {τ : Tag} {K : Type} [Field K]

theorem not_isRoot_nsmul_single_add_nsmul_single {j k : Fin τ.rank} (hjk : j ≠ k)
    (hc : τ.cartan j k = 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot τ (a • (Pi.single j 1 : Fin τ.rank → ℤ) + b • Pi.single k 1) := by
  set v : Fin τ.rank → ℤ := a • Pi.single j 1 + b • Pi.single k 1 with hv
  intro h
  have hr := IsRoot.reflect j h
  have hvl : ∀ l, v l = (if l = j then (a : ℤ) else 0) + if l = k then (b : ℤ) else 0 :=
    fun l => by simp [hv, Pi.single_apply]
  have hsum : ∑ l, τ.cartan j l * v l = 2 * a := by
    simp [hvl, mul_add, Finset.sum_add_distrib, τ.cartan_self, hc]
  have hvj : v j = a := by simp [hvl, hjk]
  have hvk : v k = b := by simp [hvl, hjk.symm]
  have hj : reflect τ j v j = -a := by
    have h1 : reflect τ j v j = v j - ∑ l, τ.cartan j l * v l := by simp [reflect]
    rw [h1, hsum, hvj]
    ring
  have hk : reflect τ j v k = b := by rw [reflect_apply_of_ne j hjk.symm, hvk]
  rcases hr.nonneg_or_nonpos with h1 | h1
  · have := h1 j
    omega
  · have := h1 k
    omega

end Native
end CFSG.LieType.Chevalley
end
