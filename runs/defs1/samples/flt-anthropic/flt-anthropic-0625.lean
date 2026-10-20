namespace P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

namespace AlgHomSpreadDirected

open TensorProduct

variable {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))

scoped instance directedSystem_F : DirectedSystem G fun i j h => ⇑(F f i j h) := by
  change DirectedSystem G fun i j h => ⇑(f i j h)
  infer_instance

section Tensor

variable (B : Type w₂) [CommRing B] [Algebra R₀ B]

noncomputable def Φ :
    R ⊗[R₀] B ≃ₗ[R₀] Module.DirectLimit (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) :=
  (limEquiv f hR).symm.rTensor B ≪≫ₗ TensorProduct.directLimitLeft (F f) B

end Tensor
end AlgHomSpreadDirected
end P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
