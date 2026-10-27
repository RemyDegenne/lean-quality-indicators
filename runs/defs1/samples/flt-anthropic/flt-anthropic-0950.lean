namespace P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_det_mem_integers_mul_relIndex_of_not_isSigmaConjugate_scalar

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

open Set Function

open scoped Pointwise NNReal

noncomputable section

p2m_reactivate

namespace ISMain

open L1Toolkit L1Main Matrix

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K

local notation "E" => L ⊗[K] v.adicCompletion K

local notation "M2" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)

local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

local notation "MF" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  secondCountableTopology_E isScalarTower_FEE smulCommClass_FEE

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L)
  (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))
  (SΛ : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
  (hSΛ : SΛ = (AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ (i : ι) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧ X = (b i).map (fun l : L => l ⊗ₜ[K] a)}))

def Obox : Set (ι → F) := {a | ∀ k, a k ∈ v.adicCompletionIntegers K}

end ISMain
end
end P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_det_mem_integers_mul_relIndex_of_not_isSigmaConjugate_scalar
