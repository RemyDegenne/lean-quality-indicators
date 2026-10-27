@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The unit `1 + εr`, with inverse `1 - εr`. -/
def liftUnit (r : R) : (DualNumber R)ˣ :=
  ⟨(1, r), (1, -r),
    by
      apply TrivSqZeroExt.ext
      · change (1 : R) * 1 = 1
        simp
      · change (1 : R) * -r + r * 1 = 0
        ring,
    by
      apply TrivSqZeroExt.ext
      · change (1 : R) * 1 = 1
        simp
      · change (1 : R) * r + -r * 1 = 0
        ring⟩

end Matrix.DualNumberKernels
end
