namespace P2MW.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal Pointwise

noncomputable section

namespace AutomorphicForm

namespace BaseChangeUnitSectionFnR

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Main

variable (σ : L ≃ₐ[K] L) (δ : Gt K L)

variable {σ δ}

variable (σ δ) (S : Finset (HeightOneSpectrum (𝓞 K)))
  (φ : Gt K L → ℂ) (φa : Ht K L → ℂ) (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)

variable {σ δ S φ φa φS} {τ : Measure (Tad σ δ)} {w : Gt K L → ℝ} {x₀ : Gt K L}

namespace Data

variable (D : Data σ δ S φ φa φS τ w x₀)

include D

theorem tensorPlace_mem_mul {x : Gt K L} (hx : φ (tconj σ δ x) ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    tensorPlace K L v x ∈ (Tv σ δ v : Set (Gsl K L v)) * (tensorPlace K L v '' tsupport w) := by
  obtain ⟨t, ht⟩ := D.exists_translate_mem hx
  refine ⟨(tensorPlace K L v (t : Gt K L))⁻¹, (Tv σ δ v).inv_mem (tensorPlace_mem_Tv t v),
    tensorPlace K L v ((t : Gt K L) * x), ⟨_, ht, rfl⟩, ?_⟩
  simp only [map_mul, inv_mul_cancel_left]

end Data
end Main
end BaseChangeUnitSectionFnR
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant
