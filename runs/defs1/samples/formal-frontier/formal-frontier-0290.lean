@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

section CoefficientChange

variable {S : Type w} [CommRing S] (f : R →+* S)

/-- Coefficient change on the SL identity fibers. -/
def slKerMap : (slReduce R n).ker →* (slReduce S n).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.map (DualNumber.mapRingHom f) g.1, by
    have h : slReduce S n (Matrix.SpecialLinearGroup.map (DualNumber.mapRingHom f) g.1) =
        Matrix.SpecialLinearGroup.map f (slReduce R n g.1) := by
      apply Subtype.ext
      rfl
    change slReduce S n (Matrix.SpecialLinearGroup.map (DualNumber.mapRingHom f) g.1) = 1
    rw [h, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

end CoefficientChange
end Matrix.DualNumberKernels
end
