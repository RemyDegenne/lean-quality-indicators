public section

noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite

open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Γ" => zigzagAlgebraInternalGrading k G

local notation "U" => zigzagGradedBraidBimodule k G

local notation "T" => GradedModuleCat.bimoduleTensorObj Γ Γ Γ

local notation "E" => zigzagBraidEvaluationHom k G

/-- Evaluate the first vertex factor of a balanced tensor product. -/
def zigzagBraidTensorEvaluationLeft (i j : V) : T (U i) (U j) ⟶ U j :=
  GradedModuleCat.bimoduleTensorMap Γ Γ Γ (E i) (𝟙 (U j)) ≫
    (zigzagBimoduleLeftUnitor k G (U j)).hom

end TauCeti
end
end
