@[expose] public section

universe u v w w₁ w₂

open Function

@[inherit_doc]
notation:25 L " →ₗ⁅" R:25 "⁆ " L':0 => LieHom R L L'

@[inherit_doc]
notation:50 L " ≃ₗ⁅" R "⁆ " L' => LieEquiv R L L'

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
  { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

end LieEquiv
end
