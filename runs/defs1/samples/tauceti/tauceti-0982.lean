public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {ι : Type v} {κ : Type w}

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

attribute [local instance] TauCeti.moduleNNRat

/-- The canonical map from the tensor square of a Kostant form over `ℤ` to the tensor square of
the ambient universal enveloping algebra over `ℚ`.

On pure tensors this is `x ⊗ y ↦ (x : U(L)) ⊗ (y : U(L))`. -/
noncomputable def kostantTensorMap (e : ι → L) (h : κ → L) :
    kostantForm e h ⊗[ℤ] kostantForm e h →ₐ[ℤ] U ⊗[ℚ] U :=
  Subring.tensorSquareMap ℚ (kostantForm e h)

end TauCeti.UniversalEnvelopingAlgebra
end
