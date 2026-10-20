@[expose] public section

set_option warningAsError true

universe u v w

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem glKerMap_conj {S : Type w} [CommRing S] (f : R →+* S)
    (h : Matrix.GeneralLinearGroup n (DualNumber R)) (k : (glReduce R n).ker) :
    glKerMap f (MulAut.conjNormal h k) =
      MulAut.conjNormal (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) h)
        (glKerMap f k) := by
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) (h * k.1 * h⁻¹) =
    Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) h *
      Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) k.1 *
      (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) h)⁻¹
  simp

end Matrix.DualNumberKernels
end
