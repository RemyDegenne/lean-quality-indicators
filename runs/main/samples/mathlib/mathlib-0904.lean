public section

variable {R : Type*} [CommRing R]

namespace Polynomial

section Field

variable (K : Type*) [Field K] [Algebra R[X] K] [FaithfulSMul R[X] K]

section NDenominators

open algebraMap

theorem quo_add_sum_rem_div_unique {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j))
    {q₁ q₂ : R[X]} {r₁ r₂ : ι → R[X]}
    (hr₁ : ∀ i ∈ s, (r₁ i).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, (r₂ i).degree < (g i).degree)
    (hf : ↑q₁ + ∑ i ∈ s, (r₁ i : K) / (g i : K) = ↑q₂ + ∑ i ∈ s, (r₂ i : K) / (g i : K)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  have : Nontrivial R :=
    have : Nontrivial R[X] := Module.nontrivial R[X] K
    Module.nontrivial R R[X]
  have hgi (i : ι) (hi : i ∈ s) : (algebraMap R[X] K (g i))⁻¹ * algebraMap R[X] K (g i) = 1 :=
    inv_mul_cancel₀ (by simpa using (hg i hi).ne_zero)
  refine (quo_add_sum_rem_mul_pow_inverse_unique (n := fun _ => 1)
      hg hcop hgi (fun i hi _ => hr₁ i hi) (fun i hi _ => hr₂ i hi) ?_).imp_right
      fun h i hi => congrFun (h i hi) 0
  simp_rw [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one, ← div_eq_mul_inv]
  exact hf

end NDenominators
end Field
end Polynomial
end
