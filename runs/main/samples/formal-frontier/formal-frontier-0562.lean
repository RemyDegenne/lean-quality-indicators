public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

@[simp]
theorem vectorGroupCoordinateBialgHom_id :
    vectorGroupCoordinateBialgHom K V V LinearMap.id =
      BialgHom.id K (vectorGroupCoordinateRing K V) := by
  apply BialgHom.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  ext φ
  simp

end AlgebraicGeometry
end
end
