@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- Special-linear first-component reduction. -/
abbrev slReduce (R : Type u) [CommRing R] (n : Type v) [Fintype n] [DecidableEq n] :
    Matrix.SpecialLinearGroup n (DualNumber R) →* Matrix.SpecialLinearGroup n R :=
  Matrix.SpecialLinearGroup.map (DualNumber.fstRingHom R)

end Matrix.DualNumberKernels
end
