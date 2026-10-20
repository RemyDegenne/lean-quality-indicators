public section

open Filter Topology

open scoped ENNReal ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {I R M : Type*} [TopologicalSpace I]

section Construction

open scoped TauCeti.RingOpNorm

variable [SeminormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

variable [DiscreteTopology I]

variable [IsUltrametricDist M] [CompleteSpace M]

variable (R) in
/-- The **linear combination map** of a bounded family `e` in a complete ultrametric module: the
continuous linear map `C₀(I, R) →L[R] M` sending `a` to the unconditional sum `∑' i, a i • e i`.
It sends the coordinate vector `single i 1` to `e i`. -/
noncomputable def linearCombination (e : lp (fun _ : I ↦ M) ∞) : C₀(I, R) →L[R] M :=
  LinearMap.mkContinuous
    { toFun a := ∑' i, a i • e i
      map_add' a b := by
        simp only [coe_add, Pi.add_apply, add_smul]
        exact (summable_smul a e).tsum_add (summable_smul b e)
      map_smul' c a := by
        simp only [coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_smul a e).tsum_const_smul c }
    ‖e‖ fun a ↦ a.norm_tsum_smul_le e

end Construction
end ZeroAtInftyContinuousMap
end
