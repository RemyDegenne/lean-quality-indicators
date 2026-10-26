/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import VectorBundles.Topology.VectorBundle.SemilinearEvaluation

/-!
# Hermitian fiber metrics

`Bundle.HermitianMetric` is a family of positive-definite Hermitian forms with topological
compatibility conditions at zero. When the fiber operations are continuous, these conditions
ensure that the induced norms give the existing fiber topologies.
`Bundle.ContinuousHermitianMetric` additionally requires continuity as a section of Mathlib's
iterated bundle of continuous semilinear maps. The scalar field is `RCLike`, so both real
symmetric and complex Hermitian metrics are included. Over `ℝ`, the equivalences
`Bundle.HermitianMetric.realEquiv` and `Bundle.ContinuousHermitianMetric.realEquiv` identify
these data with Mathlib's Riemannian metric data; no additional real metric class is introduced.

## Implementation notes

Only the fixed model fiber is normed; the bundle fibers have their original topological and
algebraic structures. The inner Hom is ordinary linear, so its joint scalar action, needed for
the outer Hom-bundle topology, is already supplied by Mathlib even for unnormed fibers.
Diagonal continuity for the conversion to `HermitianMetric` is proved by transport to a model
fiber. The bounded unit sublevel and diagonal continuity allow use of
`InnerProductSpace.Core.toNormedAddCommGroupOfTopology` and
`InnerProductSpace.ofCoreOfTopology` when the original fiber operations are continuous. These
operations can themselves be transported from the model in vector-bundle applications.
This module does not register new norm or inner-product instances on the fibers.

The Core conversion and real bridges follow the Riemannian metric formalization by Sébastien
Gouëzel in `Mathlib.Topology.VectorBundle.Riemannian`. The Hom-bundle construction is due to
Heather Macbeth and Floris van Doorn.
The scalar-valued continuity API follows `ContinuousWithinAt.inner_bundle` and its variants
in Mathlib, using semilinear bundle evaluation for the conjugate-linear first argument.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017), the Hermitian remark
  following Proposition 1.2, pp. 11–12.
* Sébastien Gouëzel, `Mathlib.Topology.VectorBundle.Riemannian`.
* Heather Macbeth and Floris van Doorn, `Mathlib.Topology.VectorBundle.Hom`.
-/

@[expose] public section

open Bundle Bornology
open scoped ComplexConjugate

namespace Bundle

section Fiberwise

variable (𝕜 : Type*) [RCLike 𝕜] {B : Type*} (E : B → Type*)
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]

/-- A family of positive-definite Hermitian forms with topological compatibility conditions.
The first argument is conjugate-linear and the second is linear, as for Mathlib's inner product.
No continuity in the base is required. Over `ℝ`, this is equivalent to `RiemannianMetric E`.

Diagonal continuity and boundedness of the unit sublevel express compatibility at zero, without
choosing a norm on any fiber. When addition and scalar multiplication on each fiber are
continuous, the induced norms give the existing fiber topologies. These operations are
automatically continuous for vector-bundle fibers by transport from the model. -/
structure HermitianMetric where
  /-- The inner product on each fiber, bundled as a continuous sesquilinear map. -/
  inner (b : B) : E b →L⋆[𝕜] E b →L[𝕜] 𝕜
  /-- Hermitian symmetry. -/
  symm (b : B) (v w : E b) : conj (inner b w v) = inner b v w
  /-- Strict positivity on nonzero vectors. -/
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < RCLike.re (inner b v v)
  /-- Continuity of the quadratic form at zero. -/
  continuousAt (b : B) : ContinuousAt (fun v : E b ↦ inner b v v) 0
  /-- Boundedness of the open unit sublevel for the original topology. -/
  isVonNBounded (b : B) : IsVonNBounded 𝕜 {v : E b | RCLike.re (inner b v v) < 1}

variable {𝕜 E}

@[ext]
theorem HermitianMetric.ext {g h : HermitianMetric 𝕜 E}
    (hinner : ∀ b v w, g.inner b v w = h.inner b v w) : g = h := by
  have : g.inner = h.inner := by
    funext b
    exact ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext (hinner b v)
  cases g
  cases h
  cases this
  rfl

/-- The real part of a vector's squared length is nonnegative. -/
theorem HermitianMetric.re_inner_self_nonneg (g : HermitianMetric 𝕜 E) (b : B) (v : E b) :
    0 ≤ RCLike.re (g.inner b v v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (g.pos b v hv).le

/-- A vector has zero squared length exactly when it is zero. -/
@[simp]
theorem HermitianMetric.inner_self_eq_zero_iff (g : HermitianMetric 𝕜 E) (b : B) (v : E b) :
    g.inner b v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have := g.pos b v hv
    simp [h] at this
  · rintro rfl
    simp

/-- The inner-product Core of a Hermitian fiber metric. Together with `g.continuousAt` and
`g.isVonNBounded`, this can be used with Mathlib's topology-preserving Core constructions.
Do not use it to install a second norm on an already normed fiber. -/
@[reducible] noncomputable def HermitianMetric.toCore (g : HermitianMetric 𝕜 E) (b : B) :
    InnerProductSpace.Core 𝕜 (E b) where
  inner v w := g.inner b v w
  conj_inner_symm := g.symm b
  re_inner_nonneg := g.re_inner_self_nonneg b
  add_left v w x := by simp
  smul_left c v := by simp
  definite v h := by
    by_contra hv
    have := g.pos b v hv
    simp [h] at this

/-- The Core conversion preserves the given inner product. -/
@[simp]
theorem HermitianMetric.toCore_inner (g : HermitianMetric 𝕜 E) (b : B) (v w : E b) :
    (g.toCore b).inner v w = g.inner b v w := rfl

end Fiberwise

section RealFiberwise

variable {B : Type*} {E : B → Type*}
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]

/-- Regard Mathlib's real Riemannian metric data as Hermitian metric data over `ℝ`. -/
def HermitianMetric.ofRiemannianMetric (g : RiemannianMetric E) : HermitianMetric ℝ E where
  inner := g.inner
  symm b v w := g.symm b w v
  pos := g.pos
  continuousAt := g.continuousAt
  isVonNBounded := g.isVonNBounded

/-- A Hermitian metric over `ℝ` is Mathlib's real Riemannian metric data. -/
def HermitianMetric.toRiemannianMetric (g : HermitianMetric ℝ E) : RiemannianMetric E where
  inner := g.inner
  symm b v w := g.symm b w v
  pos := g.pos
  continuousAt := g.continuousAt
  isVonNBounded := g.isVonNBounded

@[simp]
theorem HermitianMetric.ofRiemannianMetric_inner (g : RiemannianMetric E)
    (b : B) (v w : E b) : (ofRiemannianMetric g).inner b v w = g.inner b v w := rfl

@[simp]
theorem HermitianMetric.toRiemannianMetric_inner (g : HermitianMetric ℝ E)
    (b : B) (v w : E b) : g.toRiemannianMetric.inner b v w = g.inner b v w := rfl

@[simp]
theorem HermitianMetric.toRiemannianMetric_ofRiemannianMetric (g : RiemannianMetric E) :
    (ofRiemannianMetric g).toRiemannianMetric = g := rfl

@[simp]
theorem HermitianMetric.ofRiemannianMetric_toRiemannianMetric (g : HermitianMetric ℝ E) :
    ofRiemannianMetric g.toRiemannianMetric = g := rfl

/-- Exact identification of Hermitian metric data over `ℝ` with Mathlib's Riemannian metric data. -/
@[simps apply symm_apply]
def HermitianMetric.realEquiv : HermitianMetric ℝ E ≃ RiemannianMetric E where
  toFun := HermitianMetric.toRiemannianMetric
  invFun := HermitianMetric.ofRiemannianMetric
  left_inv := HermitianMetric.ofRiemannianMetric_toRiemannianMetric
  right_inv := HermitianMetric.toRiemannianMetric_ofRiemannianMetric

end RealFiberwise

section Continuous

variable (𝕜 : Type*) [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Positive-definite Hermitian fiber metric data varying continuously as a section of the
existing iterated semilinear Hom bundle. The metric induces the original fiber topologies,
not necessarily the norm of the model. Over `ℝ`, this is equivalent to
`ContinuousRiemannianMetric F E`. -/
structure ContinuousHermitianMetric where
  /-- The inner product on each fiber. -/
  inner (b : B) : E b →L⋆[𝕜] E b →L[𝕜] 𝕜
  /-- Hermitian symmetry. -/
  symm (b : B) (v w : E b) : conj (inner b w v) = inner b v w
  /-- Strict positivity on nonzero vectors. -/
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < RCLike.re (inner b v v)
  /-- Boundedness of the open unit sublevel for the original fiber topology. -/
  isVonNBounded (b : B) : IsVonNBounded 𝕜 {v : E b | RCLike.re (inner b v v) < 1}
  /-- Continuity as a section of Mathlib's iterated semilinear Hom bundle. -/
  continuous : Continuous
    (fun b : B ↦ TotalSpace.mk' (F →L⋆[𝕜] F →L[𝕜] 𝕜) b (inner b))

variable {𝕜 F E}

@[ext]
theorem ContinuousHermitianMetric.ext {g h : ContinuousHermitianMetric 𝕜 F E}
    (hinner : ∀ b v w, g.inner b v w = h.inner b v w) : g = h := by
  have : g.inner = h.inner := by
    funext b
    exact ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext (hinner b v)
  cases g
  cases h
  cases this
  rfl

/-- Diagonal continuity follows by transporting the continuous sesquilinear map to the normed
model fiber. No norm or continuity of the algebraic operations on the original fiber is assumed. -/
theorem ContinuousHermitianMetric.continuousAt (g : ContinuousHermitianMetric 𝕜 F E) (b : B) :
    ContinuousAt (fun v : E b ↦ g.inner b v v) 0 := by
  let e : E b ≃L[𝕜] F := Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt F E b) _
    (FiberBundle.mem_baseSet_trivializationAt' b)
  let m : (E b →L⋆[𝕜] E b →L[𝕜] 𝕜) ≃L[𝕜] (F →L⋆[𝕜] F →L[𝕜] 𝕜) :=
    e.arrowCongrSL (e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))
  have A (v : E b) : g.inner b v v = ((fun w ↦ m (g.inner b) w w) ∘ e) v := by
    simp [m]
  simp only [A]
  fun_prop

/-- Forget continuity in the base while preserving the fiber metric and its topology. -/
def ContinuousHermitianMetric.toHermitianMetric (g : ContinuousHermitianMetric 𝕜 F E) :
    HermitianMetric 𝕜 E where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  continuousAt := g.continuousAt
  isVonNBounded := g.isVonNBounded

@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_inner
    (g : ContinuousHermitianMetric 𝕜 F E) (b : B) (v w : E b) :
    g.toHermitianMetric.inner b v w = g.inner b v w := rfl

variable {M : Type*} [TopologicalSpace M] {b : M → B} {v w : ∀ m, E (b m)}
  {s : Set M} {x : M}

/-- Evaluating a continuous Hermitian metric on two continuous families of vectors over the same
base map gives a continuous scalar-valued function within a set at a point.
Continuity of the base map follows from either total-space continuity hypothesis. -/
theorem ContinuousHermitianMetric.continuousWithinAt_inner
    (g : ContinuousHermitianMetric 𝕜 F E)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F (b m) (w m)) s x) :
    ContinuousWithinAt (fun m ↦ g.inner (b m) (v m) (w m)) s x := by
  have hb : ContinuousWithinAt b s x :=
    (FiberBundle.continuous_proj F E).continuousAt.comp_continuousWithinAt hv
  have h : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' 𝕜 (E := Bundle.Trivial B 𝕜) (b m)
        (g.inner (b m) (v m) (w m))) s x :=
    (g.continuous.continuousAt.comp_continuousWithinAt hb).clm_bundle_apply₂_semilinear
      (F₁ := F) (F₂ := F) hv hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at h
  exact h.2

/-- Evaluating a continuous Hermitian metric on two families of vectors continuous at a point
in the total space gives a scalar-valued function continuous at that point. -/
theorem ContinuousHermitianMetric.continuousAt_inner (g : ContinuousHermitianMetric 𝕜 F E)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F (b m) (v m)) x)
    (hw : ContinuousAt (fun m ↦ TotalSpace.mk' F (b m) (w m)) x) :
    ContinuousAt (fun m ↦ g.inner (b m) (v m) (w m)) x := by
  rw [← continuousWithinAt_univ] at hv hw ⊢
  exact g.continuousWithinAt_inner hv hw

/-- Evaluating a continuous Hermitian metric on two families of vectors continuous on a set
in the total space gives a scalar-valued function continuous on that set. -/
theorem ContinuousHermitianMetric.continuousOn_inner (g : ContinuousHermitianMetric 𝕜 F E)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F (b m) (v m)) s)
    (hw : ContinuousOn (fun m ↦ TotalSpace.mk' F (b m) (w m)) s) :
    ContinuousOn (fun m ↦ g.inner (b m) (v m) (w m)) s :=
  fun x hx ↦ g.continuousWithinAt_inner (hv x hx) (hw x hx)

/-- Evaluating a continuous Hermitian metric on two continuous families of vectors over the same
base map gives a continuous scalar-valued function. -/
theorem ContinuousHermitianMetric.continuous_inner (g : ContinuousHermitianMetric 𝕜 F E)
    (hv : Continuous (fun m ↦ TotalSpace.mk' F (b m) (v m)))
    (hw : Continuous (fun m ↦ TotalSpace.mk' F (b m) (w m))) :
    Continuous (fun m ↦ g.inner (b m) (v m) (w m)) := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ g.continuousAt_inner hv.continuousAt hw.continuousAt

end Continuous

section RealContinuous

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- Regard Mathlib's continuous real Riemannian metric data as continuous Hermitian metric data. -/
def ContinuousHermitianMetric.ofRiemannianMetric (g : ContinuousRiemannianMetric F E) :
    ContinuousHermitianMetric ℝ F E where
  inner := g.inner
  symm b v w := g.symm b w v
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuous := g.continuous

/-- Convert continuous Hermitian metric data over `ℝ` to Mathlib's continuous Riemannian data. -/
def ContinuousHermitianMetric.toRiemannianMetric (g : ContinuousHermitianMetric ℝ F E) :
    ContinuousRiemannianMetric F E where
  inner := g.inner
  symm b v w := g.symm b w v
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuous := g.continuous

@[simp]
theorem ContinuousHermitianMetric.ofRiemannianMetric_inner (g : ContinuousRiemannianMetric F E)
    (b : B) (v w : E b) : (ofRiemannianMetric g).inner b v w = g.inner b v w := rfl

@[simp]
theorem ContinuousHermitianMetric.toRiemannianMetric_inner (g : ContinuousHermitianMetric ℝ F E)
    (b : B) (v w : E b) : g.toRiemannianMetric.inner b v w = g.inner b v w := rfl

@[simp]
theorem ContinuousHermitianMetric.toRiemannianMetric_ofRiemannianMetric
    (g : ContinuousRiemannianMetric F E) : (ofRiemannianMetric g).toRiemannianMetric = g := rfl

@[simp]
theorem ContinuousHermitianMetric.ofRiemannianMetric_toRiemannianMetric
    (g : ContinuousHermitianMetric ℝ F E) : ofRiemannianMetric g.toRiemannianMetric = g := rfl

/-- Exact identification of continuous Hermitian metric data over `ℝ` with Mathlib's continuous
Riemannian metric data, using definitionally the same Hom-bundle topology. -/
@[simps apply symm_apply]
def ContinuousHermitianMetric.realEquiv :
    ContinuousHermitianMetric ℝ F E ≃ ContinuousRiemannianMetric F E where
  toFun := ContinuousHermitianMetric.toRiemannianMetric
  invFun := ContinuousHermitianMetric.ofRiemannianMetric
  left_inv := ContinuousHermitianMetric.ofRiemannianMetric_toRiemannianMetric
  right_inv := ContinuousHermitianMetric.toRiemannianMetric_ofRiemannianMetric

/-- The real bridge commutes with forgetting continuity. -/
@[simp]
theorem ContinuousHermitianMetric.toRiemannianMetric_toHermitianMetric
    (g : ContinuousHermitianMetric ℝ F E) :
    g.toHermitianMetric.toRiemannianMetric = g.toRiemannianMetric.toRiemannianMetric := rfl

end RealContinuous

/-- The standard continuous metric on a trivial bundle with an inner-product model.
This constructor uses the given inner product, independently of the finite-dimensional existence
construction, and needs neither finite dimension nor separation assumptions on the base. -/
noncomputable def ContinuousHermitianMetric.trivial (𝕜 : Type*) [RCLike 𝕜]
    (B : Type*) [TopologicalSpace B] (V : Type*) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :
    ContinuousHermitianMetric 𝕜 V (Bundle.Trivial B V) where
  inner _ := innerSL 𝕜
  symm _ v w := inner_conj_symm v w
  pos _ v hv := by
    rw [innerSL_apply_apply, inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  isVonNBounded _ := by
    apply NormedSpace.isVonNBounded_of_isBounded 𝕜
    apply Metric.isBounded_ball.subset (t := Metric.ball (0 : V) 1)
    intro v hv
    simp only [Set.mem_ofPred_eq, innerSL_apply_apply, inner_self_eq_norm_sq] at hv
    simpa only [Metric.mem_ball, dist_zero_right, abs_norm] using
      (sq_lt_one_iff_abs_lt_one ‖v‖).mp hv
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_id, ?_⟩
    convert! continuousAt_const (y := innerSL 𝕜 (E := V))
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]

@[simp]
theorem ContinuousHermitianMetric.trivial_inner (𝕜 : Type*) [RCLike 𝕜]
    (B : Type*) [TopologicalSpace B] (V : Type*) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : B) (v w : V) : (trivial 𝕜 B V).inner b v w = Inner.inner 𝕜 v w := rfl

end Bundle
