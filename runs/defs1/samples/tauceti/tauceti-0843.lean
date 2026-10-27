public section

noncomputable section

namespace TauCeti

open MulOpposite

open scoped TensorProduct

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)

local notation "E" => Z ⊗[k] Zᵐᵒᵖ

local notation "Γ" => zigzagAlgebraInternalGrading k G

local notation "U" => zigzagGradedBraidBimodule k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)

local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)

private local instance tensorFactorsRightModule (i : V) : Module Zᵐᵒᵖ (U i) :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)

private local instance tensorFactorsLeftModule (i : V) : Module Z (U i) :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)

/-- Extract the middle corner from the actual balanced product of two vertex bimodules. -/
def zigzagBraidTensorCornerEquiv (i j : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U j) ≃ₗ[k]
      cornerSubmodule k (e i) (e j) ⊗[k] (L i ⊗[k] R j) :=
  (GradedModuleCat.bimoduleTensorUnderlyingEquiv Γ Γ Γ (U i) (U j)).trans
    ((BalancedTensorProduct.congr (rightFactors k G i)
      (zigzagBraidBimoduleFactorsEquiv k G j)
      (rightFactors_equivariant k G i) (leftFactors_equivariant k G j)).trans
    ((BalancedTensorProduct.outerFactors k Z (R i) (L j) (L i) (R j)).trans
      (TensorProduct.congr (spanSingletonBalancedTensorProductEquivCorner k
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G j)) (LinearEquiv.refl k _))))

end TauCeti
end
end
