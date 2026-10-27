@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Native SL matrices evaluate the universal GL matrix through the Hopf quotient. -/
def specialLinearFromSL (s : Matrix.SpecialLinearGroup n R) :
    SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R :=
  Ideal.Quotient.liftₐ (determinantOneIdeal K n)
    (evaluate (K := K) (Matrix.SpecialLinearGroup.toGL s)) (by
      intro element membership
      obtain ⟨multiplier, hmultiplier⟩ := Ideal.mem_span_singleton'.mp membership
      rw [← hmultiplier, map_mul, map_sub, map_one, evaluate_det]
      have hdet : (Matrix.SpecialLinearGroup.toGL s : Matrix n n R).det = 1 :=
        s.property
      rw [hdet, sub_self, mul_zero])

end AlgebraicGeometry
end
end
