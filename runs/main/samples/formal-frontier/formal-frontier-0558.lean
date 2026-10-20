@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

variable (indexType : Type u) [Fintype indexType] [DecidableEq indexType]
  (basis : Module.Basis indexType K V)

theorem specialLinearModuleMatrixEquiv_natural (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleMatrixEquiv K V indexType basis S
        (specialLinearModuleBaseChange K V R S g f) =
      Matrix.SpecialLinearGroup.map g.toRingHom
        (specialLinearModuleMatrixEquiv K V indexType basis R f) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [specialLinearModuleMatrixEquiv_toGL,
    specialLinearModuleBaseChange_toGL,
    generalLinearModuleMatrixEquiv_natural]
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  rfl

end AlgebraicGeometry
end
end
