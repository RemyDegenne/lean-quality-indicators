namespace P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel AutomorphicForm.glBorelOf

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions

namespace S5asm

p2m_open

open scoped Classical

attribute [local instance] AutomorphicForm.glBorelOf

section main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (σ : L ≃ₐ[K] L)
  (ν' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
  (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
  (a : (InfiniteAdeleRing K)ˣ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
  (M₀ : Measure (GL (Fin 2) (InfiniteAdeleRing K)))

def ValSet (b : (InfiniteAdeleRing K)ˣ) : Set ℂ :=
  {J | ∃ (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (τ' : Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)),
        normString K L (InfiniteAdeleRing K) σ δ =
          toTensorGL K L (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) ∧
        τ'.IsHaarMeasure ∧
        Measure.map (Subtype.val : twistedCentralizer K L (InfiniteAdeleRing K) σ δ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) τ' =
          Measure.map (toTensorGL K L (InfiniteAdeleRing K)) M₀ ∧
        IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν' wt δ τ' (φa ∘ archIdentGL K L) J}

end main
end S5asm
end P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
