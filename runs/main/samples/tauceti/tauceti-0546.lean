public section

namespace TauCeti

open _root_.CliffordAlgebra Module

variable {K : Type*} [Field K]

section Polarization

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q) (hline : P.line = ⊥)

variable (b : Basis (Fin 3) K P.W)

variable [Invertible (2 : K)]

section Transvections

attribute [local simp] baseAfterMatrix baseBeforeMatrix Matrix.transvection Matrix.one_apply
  Matrix.single_apply Finsupp.single_apply

@[simp]
theorem spinSixTransvectionLift_zero {i j : Fin 4} (hij : i ≠ j) :
    spinSixTransvectionLift P hline b hij 0 = 1 := by
  rw [spinSixTransvectionLift]
  apply spinTransvection_eq_one_of_mem_span
  rw [spinSixTransvectionSecondVector_zero]
  exact Submodule.zero_mem _

end Transvections
end Polarization
end TauCeti
end
