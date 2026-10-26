/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integration of continuous complex-vector-valued functions

Bochner integration on a compact measured space defines a bounded complex-linear map on
continuous functions. On the angular cube, division by its volume gives a contractive
averaging operator, including for the zero-dimensional cube.
-/

set_option warningAsError true

@[expose] public section

open MeasureTheory Set

universe u v

namespace ContinuousMap

variable {X : Type u} {F : Type v} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup F]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- A continuous function on a compact space is Bochner-integrable for any finite Borel measure. -/
theorem integrable (f : C(X, F)) : Integrable (fun x => f x) μ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    f.continuous.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
      MeasurableSet.univ Subset.rfl (measure_ne_top μ univ)

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- The linear map underlying Bochner integration of continuous functions. -/
noncomputable def integralLinearMap : C(X, F) →ₗ[ℂ] F where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := by
    simpa only [ContinuousMap.coe_add, Pi.add_apply] using
      (integral_add (integrable μ f) (integrable μ g))
  map_smul' c f := by
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact integral_smul c (fun x => f x)

omit [CompleteSpace F] in
@[simp]
theorem integralLinearMap_apply (f : C(X, F)) :
    integralLinearMap μ f = ∫ x, f x ∂μ := rfl

/-- Bochner integration of continuous functions as a continuous complex-linear map. -/
noncomputable def integralCLM : C(X, F) →L[ℂ] F :=
  (integralLinearMap μ).mkContinuous (μ.real univ) (fun f => by
    rw [integralLinearMap_apply]
    simpa only [mul_comm (‖f‖) (μ.real univ)] using
      (norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall fun x =>
        f.norm_coe_le_norm x)))

omit [CompleteSpace F] in
@[simp]
theorem integralCLM_apply (f : C(X, F)) : integralCLM μ f = ∫ x, f x ∂μ := rfl

omit [CompleteSpace F] in
/-- The operator norm of integration is bounded by the total mass of the measure. -/
theorem norm_integralCLM_le : ‖integralCLM (F := F) μ‖ ≤ μ.real univ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Integration sends a constant function to its value scaled by the total mass. -/
@[simp]
theorem integralCLM_const (value : F) :
    integralCLM μ (ContinuousMap.const X value) = μ.real univ • value := by
  simp [integralCLM_apply]

end ContinuousMap

/-- The compact cube of angular parameters for an `n`-fold circle integral. -/
abbrev angularCube (n : ℕ) : Type :=
  {θ : Fin n → ℝ // θ ∈ Set.Icc 0 (fun _ => 2 * Real.pi)}

namespace angularCube

variable (n : ℕ)

instance : CompactSpace (angularCube n) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Lebesgue measure restricted to the angular cube. -/
noncomputable instance : MeasureSpace (angularCube n) := Measure.Subtype.measureSpace

instance : IsFiniteMeasure (volume : Measure (angularCube n)) := by
  refine ⟨?_⟩
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

/-- The volume of the angular cube is `(2π)^n`, including `n = 0`. -/
theorem volume_univ : (volume (univ : Set (angularCube n))).toReal = (2 * Real.pi) ^ n := by
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  rw [Real.volume_Icc_pi_toReal (fun _ => by positivity)]
  simp

end angularCube

namespace ContinuousMap

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The normalized angular-cube integral as a bounded complex-linear map. -/
noncomputable def cubeAverageCLM (n : ℕ) : C(angularCube n, F) →L[ℂ] F :=
  (((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ)) •
    integralCLM (F := F) (volume : Measure (angularCube n))

omit [CompleteSpace F] in
/-- The average is the normalized subtype integral. -/
theorem cubeAverageCLM_apply (n : ℕ) (f : C(angularCube n, F)) :
    cubeAverageCLM (F := F) n f =
      (((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ)) • ∫ θ : angularCube n, f θ := by
  simp [cubeAverageCLM]

omit [CompleteSpace F] in
/-- Angular-cube averaging agrees with integration over the ambient closed box. -/
theorem cubeAverageCLM_apply_box (n : ℕ) (f : C(angularCube n, F))
    (g : (Fin n → ℝ) → F) (hfg : ∀ θ : angularCube n, f θ = g θ) :
    cubeAverageCLM n f = (((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ)) •
      ∫ θ in Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), g θ := by
  have heq : (∫ θ : angularCube n, f θ) = ∫ θ : angularCube n, g θ :=
    integral_congr_ae (Filter.Eventually.of_forall hfg)
  rw [cubeAverageCLM_apply, heq, integral_subtype measurableSet_Icc g]

omit [CompleteSpace F] in
/-- The average is a contraction for every dimension, including zero. -/
theorem norm_cubeAverageCLM_le (n : ℕ) : ‖cubeAverageCLM (F := F) n‖ ≤ 1 := by
  have hpos : 0 < (2 * Real.pi) ^ n := pow_pos (by positivity) _
  calc
    ‖cubeAverageCLM (F := F) n‖ ≤ ‖(((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ))‖ *
        ‖integralCLM (F := F) (volume : Measure (angularCube n))‖ := by
          simpa only [cubeAverageCLM] using
            (norm_smul_le ((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ)
              (integralCLM (F := F) (volume : Measure (angularCube n))))
    _ ≤ ‖(((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ))‖ *
        (volume (univ : Set (angularCube n))).toReal := by
      exact mul_le_mul_of_nonneg_left (norm_integralCLM_le (F := F)
        (volume : Measure (angularCube n))) (norm_nonneg _)
    _ = 1 := by
      rw [angularCube.volume_univ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos)]
      exact inv_mul_cancel₀ hpos.ne'

/-- Averaging preserves constant functions, even on the zero-dimensional cube. -/
@[simp]
theorem cubeAverageCLM_const (n : ℕ) (value : F) :
    cubeAverageCLM n (ContinuousMap.const (angularCube n) value) = value := by
  rw [cubeAverageCLM_apply]
  simp only [ContinuousMap.const_apply, integral_const]
  rw [Measure.real_def, angularCube.volume_univ]
  have hne : (2 * Real.pi) ^ n ≠ 0 := (pow_pos (by positivity) _).ne'
  calc
    (((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ)) • (((2 * Real.pi) ^ n : ℝ) • value) =
        (((2 * Real.pi) ^ n)⁻¹ : ℝ) • (((2 * Real.pi) ^ n : ℝ) • value) :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
    _ = value := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end ContinuousMap
