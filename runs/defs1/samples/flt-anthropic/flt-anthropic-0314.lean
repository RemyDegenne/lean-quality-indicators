namespace P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal Pointwise Classical

noncomputable section

namespace AutomorphicForm

namespace TwistedOrbitalEuler

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Embedding

def sMat (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => entryAdele S i j t

end Embedding
end TwistedOrbitalEuler
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
