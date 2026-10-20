@[expose] public section

namespace Matrix

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_det_le_one (A : Matrix ι ι R) (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A.det‖ ≤ 1 := by
  rw [det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro σ _
  rw [norm_units_zsmul]
  have hprod (s : Finset ι) : ‖∏ i ∈ s, A (σ i) i‖ ≤ 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (norm_mul_le _ _).trans
        ((mul_le_mul (hA (σ i) i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  exact hprod _

end Matrix
end
