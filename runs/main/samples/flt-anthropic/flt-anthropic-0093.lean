namespace P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul

set_option autoImplicit false

set_option linter.unusedSectionVars false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace K45VolB3

section Vol

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

local notation "σE" => AutomorphicForm.sigmaTensor K L (HeightOneSpectrum.adicCompletion K v) σ

omit [IsGalois K L] in
theorem iterate_mul (i : ℕ) (x y : L ⊗[K] Kv) : (⇑σE)^[i] (x * y) = (⇑σE)^[i] x * (⇑σE)^[i] y := by
  rw [← sigmaTensor_pow, ← sigmaTensor_pow, ← sigmaTensor_pow, map_mul]

end Vol
end K45VolB3
end
end P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul
