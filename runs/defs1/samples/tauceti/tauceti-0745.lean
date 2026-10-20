public section

namespace TauCeti

open MulOpposite

open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

local notation "𝒵" => AlgCat.carrier (zigzagAlgebra k G)

local notation "𝒵ᵉ" =>
  AlgCat.carrier (zigzagAlgebra k G) ⊗[k] (AlgCat.carrier (zigzagAlgebra k G))ᵐᵒᵖ

section Evaluation

variable [Finite V]

variable {k G}

variable (k G)

/-- **The evaluation `P_i ⊗_k e_i Z → Z`**, the differential of the braid complex at `i`: the map
of bimodules `x e_i ⊗ e_i y ↦ x e_i y`, the restriction of the action of the enveloping algebra on
`1`. -/
noncomputable def zigzagBraidEvaluation (i : V) :
    zigzagBraidBimodule k G i →ₗ[𝒵ᵉ] Bimodule (AlgHom.id k 𝒵) :=
  LinearMap.toSpanSingleton (𝒵ᵉ) _ (Bimodule.of (AlgHom.id k 𝒵) 1) ∘ₗ
    (zigzagBraidBimodule k G i).subtype

end Evaluation
end TauCeti
end
