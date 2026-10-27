@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- Inclusion of the SL identity fiber in the GL identity fiber. -/
def slToGL : (slReduce R n).ker →* (glReduce R n).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g.1, by
    apply Units.ext
    exact slKernel_fst g⟩
  map_one' := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Units.ext; rfl

end Matrix.DualNumberKernels
end
