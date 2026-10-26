/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Units

/-!
# Analytic Cauchy kernels with a compact parameter space

Inversion in the Banach algebra of continuous scalar functions produces a jointly analytic
finite product of coordinate kernels. At points where the denominators do not vanish, this
Banach-algebra inverse is the familiar scalar reciprocal. Multiplication by a fixed
continuous vector-valued function is a bounded complex-linear map, so it preserves
analyticity of the kernel product.
-/

set_option warningAsError true

@[expose] public section

universe u v w

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}

/-- The coordinate Cauchy kernel in the Banach algebra of continuous complex functions. -/
noncomputable def cauchyKernel (a : ι → C(X, ℂ)) (i : ι) (z : ι → ℂ) : C(X, ℂ) :=
  Ring.inverse (1 - z i • a i)

/-- The finite product of coordinate Cauchy kernels. -/
noncomputable def cauchyKernelProd (a : ι → C(X, ℂ)) (s : Finset ι)
    (z : ι → ℂ) : C(X, ℂ) :=
  ∏ i ∈ s, cauchyKernel a i z

@[simp] theorem cauchyKernel_zero (a : ι → C(X, ℂ)) (i : ι) :
    cauchyKernel a i 0 = 1 := by
  change Ring.inverse (1 - (0 : ℂ) • a i) = 1
  rw [zero_smul ℂ (a i), sub_zero, Ring.inverse_one]

@[simp] theorem cauchyKernelProd_empty (a : ι → C(X, ℂ)) (z : ι → ℂ) :
    cauchyKernelProd a ∅ z = 1 := by
  simp [cauchyKernelProd]

@[simp] theorem cauchyKernelProd_zero (a : ι → C(X, ℂ)) (s : Finset ι) :
    cauchyKernelProd a s 0 = 1 := by
  simp [cauchyKernelProd]

/-- A coordinate kernel is analytic at the origin of the coordinate space. -/
theorem analyticAt_cauchyKernel [CompactSpace X] [Fintype ι]
    (a : ι → C(X, ℂ)) (i : ι) :
    AnalyticAt ℂ (cauchyKernel a i) 0 := by
  let L : (ι → ℂ) →L[ℂ] C(X, ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ) i).smulRight (a i)
  have houter : AnalyticAt ℂ (fun y : C(X, ℂ) => Ring.inverse (1 - y)) (L 0) := by
    simpa only [map_zero] using (analyticAt_inverse_one_sub ℂ C(X, ℂ))
  have h : AnalyticAt ℂ (fun z : ι → ℂ => Ring.inverse (1 - L z)) 0 :=
    houter.compContinuousLinearMap
  change AnalyticAt ℂ (fun z : ι → ℂ => cauchyKernel a i z) 0
  convert h using 1
  funext z
  simp [cauchyKernel, L, ContinuousLinearMap.smulRight_apply]

/-- Finite products of coordinate Cauchy kernels are jointly analytic at zero. -/
theorem analyticAt_cauchyKernelProd [CompactSpace X] [Fintype ι]
    (a : ι → C(X, ℂ)) (s : Finset ι) :
    AnalyticAt ℂ (cauchyKernelProd a s) 0 := by
  change AnalyticAt ℂ (fun z : ι → ℂ => ∏ i ∈ s, cauchyKernel a i z) 0
  exact s.analyticAt_fun_prod (fun i _ => analyticAt_cauchyKernel a i)

/-- Evaluation of a Banach-algebra inverse agrees with scalar inversion when the function
has no zeros. -/
theorem ringInverse_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (Ring.inverse f) x = (f x)⁻¹ := by
  have hu : IsUnit f := (f.isUnit_iff_forall_ne_zero).2 hf
  have heval : f x * (Ring.inverse f) x = 1 := by
    simpa using congrArg (fun g : C(X, ℂ) => g x) (Ring.mul_inverse_cancel f hu)
  exact ((mul_eq_one_iff_inv_eq₀ (hf x)).mp heval).symm

/-- Evaluate a coordinate kernel when its denominator is nowhere zero. -/
theorem cauchyKernel_apply (a : ι → C(X, ℂ)) (i : ι) (z : ι → ℂ)
    (h : ∀ x, 1 - z i * a i x ≠ 0) (x : X) :
    cauchyKernel a i z x = (1 - z i * a i x)⁻¹ := by
  apply ringInverse_apply
  simpa using h

/-- Evaluate the product of coordinate kernels when all denominators are nowhere zero. -/
theorem cauchyKernelProd_apply (a : ι → C(X, ℂ)) (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i ∈ s, ∀ x, 1 - z i * a i x ≠ 0) (x : X) :
    cauchyKernelProd a s z x = ∏ i ∈ s, (1 - z i * a i x)⁻¹ := by
  simp only [cauchyKernelProd, prod_apply]
  exact Finset.prod_congr rfl (fun i hi => cauchyKernel_apply a i z (h i hi) x)

/-- For nowhere-zero boundary functions, a kernel product evaluates to the usual Cauchy
quotients wherever the boundary values differ from the corresponding coordinates. -/
theorem cauchyKernelProd_inverse_apply (ζ : ι → C(X, ℂ)) (s : Finset ι)
    (z : ι → ℂ) (hζ : ∀ i ∈ s, ∀ x, ζ i x ≠ 0)
    (hz : ∀ i ∈ s, ∀ x, ζ i x ≠ z i) (x : X) :
    cauchyKernelProd (fun i => Ring.inverse (ζ i)) s z x =
      ∏ i ∈ s, ζ i x / (ζ i x - z i) := by
  have hden (i : ι) (hi : i ∈ s) (y : X) :
      1 - z i * (Ring.inverse (ζ i)) y ≠ 0 := by
    rw [ringInverse_apply (ζ i) (hζ i hi) y]
    intro heq
    have hprod : z i * (ζ i y)⁻¹ = 1 := (sub_eq_zero.mp heq).symm
    have hzy : z i = ζ i y := by
      calc
        z i = z i * ((ζ i y)⁻¹ * ζ i y) := by rw [inv_mul_cancel₀ (hζ i hi y), mul_one]
        _ = ζ i y := by rw [← mul_assoc, hprod, one_mul]
    exact hz i hi y hzy.symm
  rw [cauchyKernelProd_apply _ s z hden x]
  apply Finset.prod_congr rfl
  intro i hi
  rw [ringInverse_apply (ζ i) (hζ i hi) x,
    eq_div_iff (sub_ne_zero.mpr (hz i hi x))]
  have hfactor : (1 - z i * (ζ i x)⁻¹) * ζ i x = ζ i x - z i := by
    calc
      (1 - z i * (ζ i x)⁻¹) * ζ i x = ζ i x - z i * ((ζ i x)⁻¹ * ζ i x) := by ring
      _ = ζ i x - z i := by simp [hζ i hi x]
  have hden' := hden i hi x
  rw [ringInverse_apply (ζ i) (hζ i hi) x] at hden'
  rw [← hfactor, ← mul_assoc, inv_mul_cancel₀ hden', one_mul]

/-- A common positive boundary radius guarantees that the kernel product evaluates to
the product of the usual Cauchy quotients. -/
theorem cauchyKernelProd_boundary_apply (ζ : ι → C(X, ℂ)) (s : Finset ι)
    (z : ι → ℂ) {R : ℝ} (hR : 0 < R)
    (hζ : ∀ i ∈ s, ∀ x, ‖ζ i x‖ = R) (hz : ∀ i ∈ s, ‖z i‖ < R) (x : X) :
    cauchyKernelProd (fun i => Ring.inverse (ζ i)) s z x =
      ∏ i ∈ s, ζ i x / (ζ i x - z i) := by
  refine cauchyKernelProd_inverse_apply ζ s z ?_ ?_ x
  · intro i hi y heq
    have hr : (0 : ℝ) = R := by simpa [heq] using hζ i hi y
    exact (ne_of_gt hR) hr.symm
  · intro i hi y heq
    have hlt : ‖z i‖ < ‖ζ i y‖ := by simpa [hζ i hi y] using hz i hi
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)

/-- The supremum norm of pointwise multiplication by a continuous complex scalar is bounded
by the product of the supremum norms. -/
theorem norm_smulRight_le [CompactSpace X]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : C(X, F)) (h : C(X, ℂ)) : ‖h • b‖ ≤ ‖b‖ * ‖h‖ := by
  apply ((h • b).norm_le (mul_nonneg (norm_nonneg b) (norm_nonneg h))).2
  intro x
  calc
    ‖(h • b) x‖ = ‖h x • b x‖ := rfl
    _ ≤ ‖h x‖ * ‖b x‖ := norm_smul_le _ _
    _ ≤ ‖b‖ * ‖h‖ := by
      rw [mul_comm ‖b‖ ‖h‖]
      gcongr
      · exact h.norm_coe_le_norm x
      · exact b.norm_coe_le_norm x

/-- A fixed vector-valued continuous function defines a bounded complex-linear multiplier
from continuous scalar functions. -/
noncomputable def smulRightCLM [CompactSpace X]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : C(X, F)) : C(X, ℂ) →L[ℂ] C(X, F) :=
  LinearMap.mkContinuous
    { toFun := fun h => h • b
      map_add' := fun h k => by ext x; simp [smul_apply', add_smul]
      map_smul' := fun c h => by ext x; simp [smul_apply', smul_smul] }
    ‖b‖ (norm_smulRight_le b)

@[simp] theorem smulRightCLM_apply [CompactSpace X]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : C(X, F)) (h : C(X, ℂ)) (x : X) :
    smulRightCLM b h x = h x • b x := rfl

/-- The operator norm of multiplication by `b` is at most the supremum norm of `b`. -/
theorem norm_smulRightCLM_le [CompactSpace X]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : C(X, F)) : ‖smulRightCLM b‖ ≤ ‖b‖ := by
  unfold smulRightCLM
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg b) (norm_smulRight_le b)

/-- Analyticity of the kernel product persists after bounded multiplication by a fixed
continuous vector-valued function. -/
theorem analyticAt_cauchyKernelProd_smul [CompactSpace X]
    {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] [Fintype ι] (a : ι → C(X, ℂ)) (s : Finset ι)
    (b : C(X, F)) :
    AnalyticAt ℂ (fun z : ι → ℂ => smulRightCLM b (cauchyKernelProd a s z)) 0 :=
  ((smulRightCLM b).analyticAt _).comp (analyticAt_cauchyKernelProd a s)

end ContinuousMap
