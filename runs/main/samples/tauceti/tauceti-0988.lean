public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}

variable [CommRing R] [CommRing A] [Algebra R A]

variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

section Field

variable {K : Type u} {L : Type v} {V : Type w}

variable [Field K] [Field L] [Algebra K L]

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]

variable {Q : QuadraticForm K V} {u w : V}

@[simp]
theorem spinGroupBaseChange_spinTransvection [Invertible (2 : L)] (hQ : Q.Nondegenerate)
    (hu : Q u = 0) (huw : QuadraticMap.polar Q u w = 0) :
    spinGroupBaseChange (A := L) Q (spinTransvection hQ hu huw) =
      spinTransvection (QuadraticForm.Nondegenerate.baseChange hQ)
        (u := 1 ⊗ₜ[K] u) (w := 1 ⊗ₜ[K] w)
        (by simp [QuadraticForm.baseChange_tmul, hu])
        (by simp [QuadraticForm.polar_baseChange_tmul, huw]) := by
  apply Subtype.ext
  rw [coe_spinGroupBaseChange_apply, coe_spinTransvection, coe_spinTransvection, map_add,
    map_one, map_mul, ofBaseChangeAux_ι, ofBaseChangeAux_ι]

end Field
end CliffordAlgebra
end
