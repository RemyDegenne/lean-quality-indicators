namespace P2MW.S_AutomorphicForm_lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory NumberField

open scoped ENNReal

noncomputable section

namespace AutomorphicForm

namespace ArchFibre

p2m_open

open scoped Classical

section Setup

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] algR

scoped instance secondCountable_Kinf : SecondCountableTopology (Kinf K) :=
  (IsHomeomorph.homeomorph _
    (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K)).secondCountableTopology

scoped instance continuousSMul_R : ContinuousSMul ℝ (Kinf K) :=
  ⟨by
    have : (fun p : ℝ × Kinf K => p.1 • p.2) = fun p => algebraMap ℝ (Kinf K) p.1 * p.2 := by
      funext p; exact Algebra.smul_def _ _
    rw [this]
    exact ((continuous_algebraMap_R K).comp continuous_fst).mul continuous_snd⟩

scoped instance mMK : MeasurableSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) := borel _

scoped instance bMK : BorelSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) := ⟨rfl⟩

scoped instance mGL : MeasurableSpace (GL (Fin 2) (Kinf K)) := AutomorphicForm.glBorelOf (Kinf K)

scoped instance bGL : BorelSpace (GL (Fin 2) (Kinf K)) := AutomorphicForm.borelSpace_glBorelOf _

scoped instance mME : MeasurableSpace (Matrix (Fin 2) (Fin 2) (Mix K)) := borel _

scoped instance bME : BorelSpace (Matrix (Fin 2) (Fin 2) (Mix K)) := ⟨rfl⟩

scoped instance bPi1 : BorelSpace (Fin 2 → Mix K) := Pi.borelSpace

scoped instance bPi2 : BorelSpace (Fin 2 → Fin 2 → Mix K) := Pi.borelSpace

scoped instance secondCountable_MK : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (Kinf K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kinf K))

scoped instance secondCountable_ME : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (Mix K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Mix K))

theorem measurable_of : Measurable fun X : Fin 2 → Fin 2 → Mix K => Matrix.of X :=
  (continuous_of K).measurable

end Setup
end ArchFibre
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
