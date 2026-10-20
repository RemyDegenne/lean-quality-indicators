public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

@[simp]
theorem coinvariants_identityComponentHopfIdeal_eq_range
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).coinvariants =
      (componentCoordinateMap H).range := by
  let C := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))
  let _ : Algebra.IsGeometricallyReduced k C := isGeometricallyReduced_of_smooth k C
  have hmap : (componentCoordinateHom H).hom.toAlgHom = componentCoordinateMap H :=
    AlgHom.ext (componentCoordinateHom_apply H)
  rw [← hmap, ← kernelHopfIdeal_componentCoordinateHom H]
  apply CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range
  apply (CommHopfAlgCat.faithfullyFlat_iff_injective_of_isGeometricallyReduced
    (componentCoordinateHom H)).mpr
  exact componentCoordinateHom_injective H

end TauCeti.FiniteTypeCommHopfAlgCat
end
