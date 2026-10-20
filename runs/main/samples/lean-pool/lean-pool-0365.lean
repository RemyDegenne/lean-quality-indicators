@[expose] public section

namespace ACMax

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

theorem fiber_entropy (hδ2 : ∀ w, 2 ≤ G.degree w) {x : V} {s' : Σ v : V, G.Walk x v}
    (hnn : ¬ s'.2.Nil) :
    ∑ s ∈ nbExtend G x s', nbWeight s * Real.log (nbWeight s)⁻¹ =
      nbWeight s' * Real.log (nbWeight s')⁻¹
        + nbWeight s' * Real.log ((G.degree s'.1 : ℝ) - 1) := by
  have hpos : 0 < nbWeight s' := nbWeight_pos hδ2 s'
  have hd2 : (2 : ℝ) ≤ (G.degree s'.1 : ℝ) := by exact_mod_cast hδ2 s'.1
  have hne : (G.degree s'.1 : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hconst : ∑ s ∈ nbExtend G x s', nbWeight s * Real.log (nbWeight s)⁻¹
      = ∑ _s ∈ nbExtend G x s',
          (nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹)
            * Real.log (nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹)⁻¹ := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [nbWeight_of_mem_nbExtend hnn hs]
  rw [hconst, Finset.sum_const, card_nbExtend hnn, nsmul_eq_mul,
    show ((G.degree s'.1 - 1 : ℕ) : ℝ) = (G.degree s'.1 : ℝ) - 1 from by
      rw [Nat.cast_sub (by have := hδ2 s'.1; omega), Nat.cast_one]]
  have hqlog : Real.log (nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹)⁻¹
      = Real.log (nbWeight s')⁻¹ + Real.log ((G.degree s'.1 : ℝ) - 1) := by
    rw [Real.log_inv, Real.log_mul (ne_of_gt hpos) (inv_ne_zero hne), Real.log_inv, Real.log_inv]
    ring
  rw [hqlog]
  field_simp

end ACMax
end
