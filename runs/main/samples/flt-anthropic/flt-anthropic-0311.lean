namespace P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace UnitTensorDescent

open TensorProduct Function

variable {R S K T : Type}
  [CommRing R] [IsDomain R]
  [CommRing S] [Algebra R S]
  [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [AddCommGroup T] [Module R T]

section WithFractionAlgebra

variable [Algebra (FractionRing R) K] [IsScalarTower R (FractionRing R) K]

variable [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K)]

omit [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K)] [IsDomain R] in

theorem baseChange_cancelBaseChange (h : T →ₗ[R] T)
    (u : K ⊗[FractionRing R] (FractionRing R ⊗[R] T)) :
    h.baseChange K (AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T u)
      = AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T
          (LinearMap.lTensor K (h.baseChange (FractionRing R)) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c y => simp
      | add z₁ z₂ ih₁ ih₂ => rw [TensorProduct.tmul_add, map_add, map_add, ih₁, ih₂,
          map_add, map_add]
  | add u₁ u₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

end WithFractionAlgebra
end UnitTensorDescent
end
end P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero
