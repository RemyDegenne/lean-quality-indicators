namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain

open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace K42CT

open MeasureTheory NumberField Topology AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions

open LanglandsTunnell.CubicInduction (diagUnits2)

section Corr

variable {G H : Type} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

noncomputable def corrEquiv (φ : G →* H) (hφ : IsClosedEmbedding φ) (C : Subgroup G) (T : Subgroup H) (y : H)
    (hCT : ∀ s ∈ C, y * φ s * y⁻¹ ∈ T) (hTC : ∀ t ∈ T, ∃ s ∈ C, φ s = y⁻¹ * t * y) : C ≃ₜ* T :=
  { MulEquiv.ofBijective (corrHom φ C T y hCT) (corrHom_bijective φ hφ.injective C T y hCT hTC) with
    continuous_toFun := by
      show Continuous (corrHom φ C T y hCT)
      exact ((continuous_const.mul (hφ.continuous.comp continuous_subtype_val)).mul continuous_const).subtype_mk _
    continuous_invFun := by
      set E := MulEquiv.ofBijective (corrHom φ C T y hCT) (corrHom_bijective φ hφ.injective C T y hCT hTC)
      show Continuous E.symm
      have hemb : IsEmbedding (fun s : C => φ (s : G)) :=
        hφ.isEmbedding.comp IsEmbedding.subtypeVal
      rw [hemb.continuous_iff]
      have hid : (fun s : C => φ (s : G)) ∘ E.symm = fun t : T => y⁻¹ * (t : H) * y := by
        funext t
        simp only [Function.comp_apply]
        have ht : ((E (E.symm t) : T) : H) = (t : H) := by rw [MulEquiv.apply_symm_apply]
        rw [show ((E (E.symm t) : T) : H) = y * φ (E.symm t : G) * y⁻¹ from rfl] at ht
        rw [← ht]; group
      rw [hid]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const }

end Corr
end K42CT
end P2MW.S_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2
