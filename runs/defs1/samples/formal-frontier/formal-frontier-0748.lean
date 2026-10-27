@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

/-- Descend evaluation of a filtered unitriangular matrix to the stage quotient. -/
def unitriangularStageFromGL
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    CoordinateRing K n r →ₐ[K] R :=
  Ideal.Quotient.liftₐ (ideal K n r)
    (unitriangularFromGL K (Fin n) R s.1) (by
      intro x hx
      have hs : unitriangularToGL K (Fin n) R
          (unitriangularFromGL K (Fin n) R s.1) ∈
          Matrix.UnitriangularGroup.superdiagonalSubgroup n R r := by
        simpa only [unitriangularToGL_fromGL] using s.2
      exact RingHom.mem_ker.mp
        ((mem_stage_iff K n r (unitriangularFromGL K (Fin n) R s.1)).mpr hs hx))

end AlgebraicGeometry
end
end
