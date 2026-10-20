@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

theorem specialLinearModuleBaseChange_toGL (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    (specialLinearModuleBaseChange K V R S g f).toGeneralLinearGroup =
      generalLinearModuleBaseChange K V R S g f.toGeneralLinearGroup := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  rfl

end AlgebraicGeometry
end
end
