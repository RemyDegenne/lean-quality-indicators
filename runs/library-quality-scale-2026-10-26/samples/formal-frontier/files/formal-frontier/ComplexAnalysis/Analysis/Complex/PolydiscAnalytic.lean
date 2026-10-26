/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.PolydiscKernel
public import ComplexAnalysis.Analysis.Complex.TorusCauchy
public import ComplexAnalysis.Analysis.Complex.TorusKernel
public import ComplexAnalysis.MeasureTheory.Integral.ContinuousMap

/-!
# Analyticity from the Cauchy formula on a polydisc

The boundary kernel is analytic as a continuous-function-valued map. Multiplication
by fixed boundary values and normalized integration are bounded linear maps. The
Cauchy formula identifies their composite with the original function near zero.
-/

@[expose] public section

open Complex Set MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- A complex-differentiable map on a closed polydisc of positive radius is analytic
at the origin, with values in any complete complex normed space. -/
theorem DifferentiableOn.analyticAt_zero_of_polydisc
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {n : ℕ} {f : (Fin n → ℂ) → F} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f {z | ∀ i, ‖z i‖ ≤ R}) :
    AnalyticAt ℂ f 0 := by
  let ζ : Fin n → C(angularCube n, ℂ) := fun i =>
    ⟨fun θ => torusMap 0 (fun _ => R) θ.1 i, by
      exact (continuous_circleMap (0 : ℂ) R).comp
        ((continuous_apply i).comp continuous_subtype_val)⟩
  have hζ (i : Fin n) (θ : angularCube n) : ‖ζ i θ‖ = R := by
    change ‖circleMap 0 R (θ.1 i)‖ = R
    rw [norm_circleMap_zero, abs_of_pos hR]
  have hboundary : Continuous (fun θ : angularCube n =>
      f (torusMap 0 (fun _ => R) θ.1)) :=
    hf.continuousOn.comp_continuous (continuous_pi (fun i => (ζ i).continuous))
      (fun θ i => (hζ i θ).le)
  let b : C(angularCube n, F) := ⟨_, hboundary⟩
  let a : Fin n → C(angularCube n, ℂ) := fun i => Ring.inverse (ζ i)
  let g : (Fin n → ℂ) → F := fun z =>
    ContinuousMap.cubeAverageCLM n
      (ContinuousMap.smulRightCLM b (ContinuousMap.cauchyKernelProd a Finset.univ z))
  have hg : AnalyticAt ℂ g 0 :=
    ((ContinuousMap.cubeAverageCLM (F := F) n).analyticAt _).comp
      (ContinuousMap.analyticAt_cauchyKernelProd_smul a Finset.univ b)
  apply hg.congr
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hR] with z hz
  have hz' : ‖z‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzi (i : Fin n) : ‖z i‖ < R := (norm_le_pi_norm z i).trans_lt hz'
  let G : (Fin n → ℝ) → F := fun θ =>
    (∏ i, torusMap 0 (fun _ => R) θ i /
      (torusMap 0 (fun _ => R) θ i - z i)) • f (torusMap 0 (fun _ => R) θ)
  have hvalues (θ : angularCube n) :
      ContinuousMap.smulRightCLM b (ContinuousMap.cauchyKernelProd a Finset.univ z) θ =
        G θ.1 := by
    rw [ContinuousMap.smulRightCLM_apply]
    have hk := ContinuousMap.cauchyKernelProd_boundary_apply ζ Finset.univ z hR
      (fun i _ θ => hζ i θ) (fun i _ => hzi i) θ
    calc
      _ = (∏ i, ζ i θ / (ζ i θ - z i)) • b θ :=
        congrArg (fun c : ℂ => c • b θ) hk
      _ = G θ.1 := rfl
  have havg : g z = (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹ •
      ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), G θ := by
    simpa only [g, Complex.ofReal_inv] using
      ContinuousMap.cubeAverageCLM_apply_box n
        (ContinuousMap.smulRightCLM b (ContinuousMap.cauchyKernelProd a Finset.univ z))
        G hvalues
  have hf' : DifferentiableOn ℂ f
      {w | ∀ i, w i ∈ Metric.closedBall (0 : ℂ) R} := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hf
  have hc := hf'.torusIntegral_cauchy (c := 0) (z := z) (R := fun _ => R)
    (fun i => by simpa only [Metric.mem_ball, Pi.zero_apply, dist_zero_right] using hzi i)
  have hn := torusIntegral_prod_inv_normalized_zero f z (fun _ => R)
  have hC : (2 * (Real.pi : ℂ) * I) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  rw [hc, smul_smul, inv_mul_cancel₀ hC, one_smul] at hn
  exact havg.trans hn.symm
