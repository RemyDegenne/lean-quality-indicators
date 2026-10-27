@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The scalar-extension algebra equivalence built from Christian Merten's
Mathlib `MvPolynomial.algebraTensorAlgEquiv` respects the two independently
given bialgebra structures, using Yaël Dillies's `BialgEquiv.ofAlgEquiv`. -/
def baseChangeBialgEquiv :
    S ⊗[R] CoordinateRing R ι ≃ₐc[S] CoordinateRing S ι := by
  let sourceBialgebra : Bialgebra S (S ⊗[R] CoordinateRing R ι) := inferInstance
  let targetBialgebra : Bialgebra S (CoordinateRing S ι) := inferInstance
  let algebraTypes :
      (S ⊗[R] CoordinateRing R ι ≃ₐ[S] CoordinateRing S ι) =
        @AlgEquiv S (S ⊗[R] CoordinateRing R ι) (CoordinateRing S ι) (inferInstance)
          (inferInstance) (inferInstance) sourceBialgebra.toAlgebra
          targetBialgebra.toAlgebra := rfl
  let bialgebraTypes :
      (S ⊗[R] CoordinateRing R ι ≃ₐc[S] CoordinateRing S ι) =
        @BialgEquiv S (inferInstance) (S ⊗[R] CoordinateRing R ι) (CoordinateRing S ι)
          (inferInstance) (inferInstance) sourceBialgebra.toAlgebra
          targetBialgebra.toAlgebra sourceBialgebra.toCoalgebra.toCoalgebraStruct
          targetBialgebra.toCoalgebra.toCoalgebraStruct := rfl
  let algebraEquiv := algebraTypes.mp (baseChange R S ι)
  have algebraEquiv_eq : algebraEquiv = baseChange R S ι := by
    dsimp [algebraEquiv, algebraTypes]
  apply bialgebraTypes.mpr
  exact BialgEquiv.ofAlgEquiv algebraEquiv
    (by rw [algebraEquiv_eq]; exact baseChange_counit R S ι)
    (by rw [algebraEquiv_eq]; exact baseChange_comul R S ι)

end UnitriangularCoordinateRing
end
end
