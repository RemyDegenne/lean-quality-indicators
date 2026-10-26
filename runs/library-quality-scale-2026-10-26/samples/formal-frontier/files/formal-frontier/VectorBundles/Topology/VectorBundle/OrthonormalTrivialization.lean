/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# Orthonormal coordinates for a continuous Hermitian metric

`Bundle.ContinuousHermitianMetric.orthonormalizeTrivialization` replaces the coordinates of
any linear trivialization by Euclidean coordinates for the supplied metric, on exactly the
same base set. The output is a `Bundle.Trivialization` on the original total space, with
coordinate fiber `EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))`. Its fiber coordinates are
linear and preserve the metric pairing. They need not preserve an unrelated original norm
on the model or fibers. No new norms or topologies on the fibers are installed.

## Implementation notes

The existence proof represents the metric by a continuous positive-definite coordinate
matrix and uses its positive square root from Mathlib's continuous functional calculus.
The public construction chooses a chart noncanonically; no fixed square-root formula is part
of its API. The arbitrary input chart need not belong to the bundle atlas, and its base set
may be empty. The Euclidean target
need not equal the original model, so fiber linearity is expressed by `IsLinearMap`, not by
`Bundle.Trivialization.IsLinear`, whose type requires the same model on both sides.

This refines the local orthogonal-frame ingredient in Hatcher's proof of Proposition 1.3.
It treats a supplied continuous Hermitian metric over `RCLike`, an arbitrary topological base,
and an arbitrary finite-dimensional normed model. It does not assert an adapted subbundle
frame, preservation of intermediate spans, a parametric Gram–Schmidt algorithm, or the whole
proposition. The formulation uses Mathlib's bundle trivializations by Floris van Doorn and
Heather Macbeth, and the Hermitian metric API extending Sébastien Gouëzel's Riemannian metrics.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017), proof of
  Proposition 1.3, printed p. 12 (PDF p. 16).
-/

@[expose] public section

open Bundle
open scoped ComplexOrder

universe u𝕜 uB uF uE

namespace Bundle.ContinuousHermitianMetric

variable {𝕜 : Type u𝕜} [RCLike 𝕜] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

section MatrixNormalization

open scoped ComplexOrder Matrix MatrixOrder

variable {κ X ι : Type*} [RCLike κ] [TopologicalSpace X] [Fintype ι]

open scoped Matrix.Norms.L2Operator in
/-- The positive square root is continuous for a continuous family of positive matrices. -/
private theorem continuous_positive_matrix_sqrt (M : X → Matrix ι ι κ)
    (hM : Continuous M) (hpos : ∀ x, (M x).PosDef) :
    open scoped Classical in Continuous (fun x ↦ CFC.sqrt (M x)) := by
  classical
  -- Restriction of the scalar norm bound preserves the existing matrix scalar action.
  let : NormedAlgebra ℝ (Matrix ι ι κ) :=
    { norm_smul_le := fun r A ↦ by
        have h := norm_smul_le (algebraMap ℝ κ r) A
        simpa only [algebraMap_smul, norm_algebraMap'] using h }
  exact (CFC.continuousOn_sqrt (A := Matrix ι ι κ)).comp_continuous hM
    fun x ↦ (hpos x).posSemidef.nonneg

/-- Positive square roots give continuously varying Euclidean coordinates for a positive
matrix pairing. Both the coordinates and their inverses are jointly continuous. The construction
uses Mathlib's continuous functional calculus and `Matrix.toEuclideanCLM`. -/
private theorem exists_positive_matrix_normalization (M : X → Matrix ι ι κ)
    (hM : Continuous M) (hpos : ∀ x, (M x).PosDef) :
    ∃ a : X → EuclideanSpace κ ι ≃L[κ] EuclideanSpace κ ι,
      Continuous (fun p : X × EuclideanSpace κ ι ↦ a p.1 p.2) ∧
      Continuous (fun p : X × EuclideanSpace κ ι ↦ (a p.1).symm p.2) ∧
      ∀ x u v, Inner.inner κ (a x u) (a x v) =
        dotProduct (star (fun i ↦ u i)) ((M x).mulVec (fun i ↦ v i)) := by
  classical
  let S : X → Matrix ι ι κ := fun x ↦ CFC.sqrt (M x)
  have hS : Continuous S :=
    continuous_positive_matrix_sqrt M hM hpos
  have hunit (x : X) : IsUnit (S x) :=
    IsStrictlyPositive.isUnit_cfcSqrt (M x) (hpos x).isStrictlyPositive
  let U : X → (Matrix ι ι κ)ˣ := fun x ↦ (hunit x).unit
  have hU : Continuous U := by
    apply Units.continuous_iff.mpr
    constructor
    · simpa only [U, IsUnit.unit_spec, Function.comp_def] using hS
    · simp_rw [Matrix.coe_units_inv, show ∀ x, (↑(U x) : Matrix ι ι κ) = S x
        from fun x ↦ (hunit x).unit_spec]
      apply continuous_iff_continuousAt.mpr
      intro x
      apply (continuousAt_matrix_inv (S x) ?_).comp hS.continuousAt
      convert NormedRing.inverse_continuousAt ((hunit x).map Matrix.detMonoidHom).unit using 1
      exact ((hunit x).map Matrix.detMonoidHom).unit_spec.symm
  let a : X → EuclideanSpace κ ι ≃L[κ] EuclideanSpace κ ι := fun x ↦
    ContinuousLinearEquiv.ofUnit
      (Units.map ((Matrix.toEuclideanCLM (𝕜 := κ) (n := ι)).toMonoidHom) (U x))
  have ha (x : X) (u : EuclideanSpace κ ι) :
      a x u = Matrix.toEuclideanCLM (𝕜 := κ) (n := ι) (S x) u := by
    change Matrix.toEuclideanCLM (𝕜 := κ) (n := ι) (↑(U x)) u = _
    rw [show ↑(U x) = S x from (hunit x).unit_spec]
  refine ⟨a, ?_, ?_, ?_⟩
  · simp_rw [ha]
    have hp : Continuous (fun p : X × EuclideanSpace κ ι ↦ (S p.1, p.2)) :=
      (hS.comp continuous_fst).prodMk continuous_snd
    simpa only [Function.comp_def] using
      (Matrix.continuous_uncurry_toEuclideanCLM (𝕜 := κ) (n := ι)).comp hp
  · change Continuous (fun p : X × EuclideanSpace κ ι ↦
      Matrix.toEuclideanCLM (𝕜 := κ) (n := ι) (↑((U p.1)⁻¹)) p.2)
    have hp : Continuous (fun p : X × EuclideanSpace κ ι ↦ ((↑((U p.1)⁻¹) : Matrix ι ι κ), p.2)) :=
      ((Units.continuous_coe_inv.comp hU).comp continuous_fst).prodMk continuous_snd
    simpa only [Function.comp_def] using
      (Matrix.continuous_uncurry_toEuclideanCLM (𝕜 := κ) (n := ι)).comp hp
  · intro x u v
    rw [ha, ha, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
      Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    change dotProduct (star ((S x).mulVec (fun i ↦ u i)))
      ((S x).mulVec (fun i ↦ v i)) = _
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    have hs : (S x)ᴴ * S x = M x := by
      rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg (M x)).star_eq]
      exact CFC.sqrt_mul_sqrt_self (M x) (hpos x).posSemidef.nonneg
    rw [hs, ← Matrix.dotProduct_mulVec]

end MatrixNormalization

/-- Fixed Euclidean coordinates for the original normed model. No isometry is asserted. -/
private noncomputable def modelEuclideanEquiv :
    F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The metric pulled back to fixed Euclidean coordinates on a chart's base set. -/
private noncomputable def coordinateForm (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet) :
    EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) →ₗ⋆[𝕜]
      EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) →ₗ[𝕜] 𝕜 :=
  let r := (e.linearEquivAt 𝕜 b.1 b.2).symm.toLinearMap.comp φ.symm.toLinearMap
  ((g.inner b.1).toLinearMap₁₂.comp r).compl₂ r

omit [FiniteDimensional 𝕜 F] in
private theorem coordinateForm_apply (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet)
    (u v : EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) :
    coordinateForm g e φ b u v =
      g.inner b.1 ((e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm u))
        ((e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm v)) := rfl

/-- The matrix of the pulled-back metric in the standard coordinate basis. -/
private noncomputable def coordinateMatrix (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet) :
    Matrix (Fin (Module.finrank 𝕜 F)) (Fin (Module.finrank 𝕜 F)) 𝕜 :=
  LinearMap.toMatrix₂ (EuclideanSpace.basisFun _ 𝕜).toBasis
    (EuclideanSpace.basisFun _ 𝕜).toBasis (coordinateForm g e φ b)

omit [FiniteDimensional 𝕜 F] in
private theorem coordinateMatrix_apply (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet)
    (i j : Fin (Module.finrank 𝕜 F)) :
    coordinateMatrix g e φ b i j =
      g.inner b.1
        ((e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm (EuclideanSpace.basisFun _ 𝕜 i)))
        ((e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm (EuclideanSpace.basisFun _ 𝕜 j))) := by
  simp only [coordinateMatrix, LinearMap.toMatrix₂_apply,
    OrthonormalBasis.coe_toBasis, coordinateForm_apply]

omit [FiniteDimensional 𝕜 F] in
private theorem coordinateMatrix_pairing (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet)
    (u v : EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) :
    coordinateForm g e φ b u v =
      dotProduct (star (fun i ↦ u i)) ((coordinateMatrix g e φ b).mulVec (fun i ↦ v i)) := by
  simpa only [coordinateMatrix, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Function.comp_def, RingHom.id_apply, starRingEnd_apply,
    Pi.star_def] using
    apply_eq_dotProduct_toMatrix₂_mulVec
      (EuclideanSpace.basisFun _ 𝕜).toBasis (EuclideanSpace.basisFun _ 𝕜).toBasis
      (coordinateForm g e φ b) u v

omit [FiniteDimensional 𝕜 F] in
private theorem coordinateMatrix_posDef (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet) :
    (coordinateMatrix g e φ b).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simpa only [Matrix.conjTranspose_apply, coordinateMatrix_apply, RCLike.star_def] using
      g.symm b.1
        ((e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm (EuclideanSpace.basisFun _ 𝕜 i)))
        ((e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm (EuclideanSpace.basisFun _ 𝕜 j)))
  · intro x hx
    let u : EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) := (EuclideanSpace.equiv _ _).symm x
    have hu : u ≠ 0 := by
      intro h
      apply hx
      simpa [u] using congrArg (EuclideanSpace.equiv _ _) h
    have hr : (e.linearEquivAt 𝕜 b.1 b.2).symm (φ.symm u) ≠ 0 := by
      intro h
      apply hu
      apply φ.symm.injective
      apply (e.linearEquivAt 𝕜 b.1 b.2).symm.injective
      simpa only [map_zero] using h
    have hp : 0 < coordinateForm g e φ b u u := by
      rw [coordinateForm_apply]
      apply RCLike.pos_iff.mpr
      exact ⟨g.pos _ _ hr, RCLike.conj_eq_iff_im.mp (g.symm _ _ _)⟩
    simpa only [coordinateMatrix_pairing, u, PiLp.continuousLinearEquiv_symm_apply,
      WithLp.ofLp_toLp] using hp

omit [FiniteDimensional 𝕜 F] in
private theorem continuous_coordinateMatrix (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) :
    Continuous (coordinateMatrix g e φ) := by
  have hinv (v : F) : Continuous (fun b : e.baseSet ↦
      TotalSpace.mk' F b.1 ((e.linearEquivAt 𝕜 b.1 b.2).symm v)) := by
    have h := (e.continuousOn_symm_prodMk_left (v := v)).comp_continuous
      continuous_subtype_val (fun b ↦ b.2)
    exact h.congr (fun b ↦ (e.mk_symm b.2 v).symm)
  apply continuous_matrix
  intro i j
  simp only [coordinateMatrix_apply]
  exact g.continuous_inner (hinv _) (hinv _)

omit [FiniteDimensional 𝕜 F] in
private theorem coordinateMatrix_inner (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (b : e.baseSet)
    (v w : E b.1) :
    g.inner b.1 v w =
      dotProduct (star (fun i ↦ φ (e.linearEquivAt 𝕜 b.1 b.2 v) i))
        ((coordinateMatrix g e φ b).mulVec (fun i ↦ φ (e.linearEquivAt 𝕜 b.1 b.2 w) i)) := by
  simpa only [coordinateForm_apply, ContinuousLinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply] using coordinateMatrix_pairing g e φ b
      (φ (e.linearEquivAt 𝕜 b.1 b.2 v)) (φ (e.linearEquivAt 𝕜 b.1 b.2 w))

/-- A continuous positive-definite matrix representation in one fixed Euclidean model. -/
private theorem exists_coordinateMatrix (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    ∃ φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)),
      ∃ M : e.baseSet → Matrix (Fin (Module.finrank 𝕜 F)) (Fin (Module.finrank 𝕜 F)) 𝕜,
        Continuous M ∧ (∀ b, (M b).PosDef) ∧
        ∀ b : e.baseSet, ∀ v w : E b.1,
          g.inner b.1 v w =
            dotProduct (star (fun i ↦ φ (e.linearEquivAt 𝕜 b.1 b.2 v) i))
              ((M b).mulVec (fun i ↦ φ (e.linearEquivAt 𝕜 b.1 b.2 w) i)) := by
  let φ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) := modelEuclideanEquiv
  exact ⟨φ, coordinateMatrix g e φ, continuous_coordinateMatrix g e φ,
    coordinateMatrix_posDef g e φ, coordinateMatrix_inner g e φ⟩

omit [FiniteDimensional 𝕜 F] in
/-- Jointly continuous changes of fiber coordinates assemble to a chart on the same
base set and the same total space. -/
private theorem exists_orthonormalization_of_coordinates
    (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ₀ : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)))
    (a : e.baseSet → F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)))
    (ha : Continuous (fun p : e.baseSet × F ↦ a p.1 p.2))
    (haInv : Continuous (fun p : e.baseSet ×
      EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) ↦ (a p.1).symm p.2))
    (haInner : ∀ b : e.baseSet, ∀ v w : E b.1,
      Inner.inner 𝕜 (a b (e.linearEquivAt 𝕜 b.1 b.2 v))
        (a b (e.linearEquivAt 𝕜 b.1 b.2 w)) = g.inner b.1 v w) :
    ∃ c : Trivialization (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (π F E),
      c.baseSet = e.baseSet ∧
      (∀ b ∈ e.baseSet,
        IsLinearMap 𝕜 (fun v : E b ↦ (c (TotalSpace.mk' F b v)).2)) ∧
      ∀ b ∈ e.baseSet, ∀ v w : E b,
        Inner.inner 𝕜 (c (TotalSpace.mk' F b v)).2 (c (TotalSpace.mk' F b w)).2 =
          g.inner b v w := by
  classical
  let H := EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))
  -- Values outside the chart are arbitrary; continuity is used only on the open base set.
  let a' : B → F ≃L[𝕜] H := fun b ↦ if hb : b ∈ e.baseSet then a ⟨b, hb⟩ else φ₀
  have ha' (b : B) (hb : b ∈ e.baseSet) : a' b = a ⟨b, hb⟩ := dite_eq_left hb
  let f : B × F → B × H := fun p ↦ (p.1, a' p.1 p.2)
  let fInv : B × H → B × F := fun p ↦ (p.1, (a' p.1).symm p.2)
  have hf : ContinuousOn f (e.baseSet ×ˢ Set.univ) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let m : (e.baseSet ×ˢ (Set.univ : Set F)) → e.baseSet × F :=
      fun p ↦ (⟨p.1.1, p.2.1⟩, p.1.2)
    have hm : Continuous m :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
    convert continuous_subtype_val.fst.prodMk (ha.comp hm) using 1
    funext p
    simp only [Set.domRestrict, f, m, ha' _ p.2.1, Function.comp_apply]
  have hfInv : ContinuousOn fInv (e.baseSet ×ˢ Set.univ) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let m : (e.baseSet ×ˢ (Set.univ : Set H)) → e.baseSet × H :=
      fun p ↦ (⟨p.1.1, p.2.1⟩, p.1.2)
    have hm : Continuous m :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
    convert continuous_subtype_val.fst.prodMk (haInv.comp hm) using 1
    funext p
    simp only [Set.domRestrict, fInv, m, ha' _ p.2.1, Function.comp_apply]
  let c : Trivialization H (π F E) :=
    { toFun := fun p ↦ f (e p)
      invFun := fun p ↦ e.toOpenPartialHomeomorph.symm (fInv p)
      source := e.source
      target := e.baseSet ×ˢ Set.univ
      map_source' := by
        intro p hp
        exact ⟨e.mem_target.mp (e.toOpenPartialHomeomorph.map_source hp), Set.mem_univ _⟩
      map_target' := by
        intro p hp
        exact e.map_target (e.mem_target.mpr hp.1)
      left_inv' := by
        intro p hp
        change e.toOpenPartialHomeomorph.symm
          ((e p).1, (a' (e p).1).symm (a' (e p).1 (e p).2)) = p
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact e.toOpenPartialHomeomorph.left_inv hp
      right_inv' := by
        intro p hp
        change f (e (e.toOpenPartialHomeomorph.symm (fInv p))) = p
        rw [e.apply_symm_apply (e.mem_target.mpr hp.1)]
        exact Prod.ext rfl ((a' p.1).apply_symm_apply p.2)
      open_source := e.open_source
      open_target := e.open_baseSet.prod isOpen_univ
      continuousOn_toFun := hf.comp e.toOpenPartialHomeomorph.continuousOn (by
        intro p hp
        exact ⟨e.mem_target.mp (e.toOpenPartialHomeomorph.map_source hp), Set.mem_univ _⟩)
      continuousOn_invFun := e.toOpenPartialHomeomorph.continuousOn_symm.comp hfInv (by
        intro p hp
        exact e.mem_target.mpr hp.1)
      baseSet := e.baseSet
      open_baseSet := e.open_baseSet
      source_eq := e.source_eq
      target_eq := rfl
      proj_toFun := e.proj_toFun }
  have hc (b : B) (hb : b ∈ e.baseSet) (v : E b) :
      (c (TotalSpace.mk' F b v)).2 = a ⟨b, hb⟩ (e.linearEquivAt 𝕜 b hb v) := by
    change a' (e (TotalSpace.mk' F b v)).1 (e (TotalSpace.mk' F b v)).2 = _
    rw [e.coe_fst' hb, ha' b hb]
    rfl
  refine ⟨c, rfl, ?_, ?_⟩
  · intro b hb
    have hlin := ((a ⟨b, hb⟩).toLinearEquiv.toLinearMap.comp
      (e.linearEquivAt 𝕜 b hb).toLinearMap).isLinear
    convert hlin using 1
    funext v
    exact hc b hb v
  · intro b hb v w
    rw [hc b hb v, hc b hb w]
    exact haInner ⟨b, hb⟩ v w

/-- Normalization on the entire base set of an arbitrary linear chart, without changing
the original total-space topology. -/
private theorem exists_orthonormalization (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    ∃ c : Trivialization (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (π F E),
      c.baseSet = e.baseSet ∧
      (∀ b ∈ e.baseSet,
        IsLinearMap 𝕜 (fun v : E b ↦ (c (TotalSpace.mk' F b v)).2)) ∧
      ∀ b ∈ e.baseSet, ∀ v w : E b,
        Inner.inner 𝕜 (c (TotalSpace.mk' F b v)).2 (c (TotalSpace.mk' F b w)).2 =
          g.inner b v w := by
  obtain ⟨φ, M, hM, hpos, hpair⟩ := exists_coordinateMatrix g e
  obtain ⟨β, hβ, hβInv, hβInner⟩ := exists_positive_matrix_normalization M hM hpos
  let α : e.baseSet → F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) :=
    fun b ↦ φ.trans (β b)
  apply exists_orthonormalization_of_coordinates g e φ α
  · exact hβ.comp (continuous_fst.prodMk (φ.continuous.comp continuous_snd))
  · exact φ.symm.continuous.comp hβInv
  · intro b v w
    exact (hβInner b (φ (e.linearEquivAt 𝕜 b.1 b.2 v))
      (φ (e.linearEquivAt 𝕜 b.1 b.2 w))).trans (hpair b v w).symm

/-- Euclidean coordinates for the supplied Hermitian metric on exactly the base set of `e`.
The chart acts on the original total space; metric preservation is not an assertion about
unrelated preexisting norms. The chart is chosen noncanonically. -/
@[no_expose]
noncomputable def orthonormalizeTrivialization (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    Trivialization (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (π F E) :=
  (exists_orthonormalization g e).choose

/-- Normalization preserves the entire base set, including an empty base set. -/
@[simp]
theorem orthonormalizeTrivialization_baseSet (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    (g.orthonormalizeTrivialization e).baseSet = e.baseSet :=
  (exists_orthonormalization g e).choose_spec.1

/-- The normalized coordinates are linear on each fiber over the chart's base set. -/
theorem orthonormalizeTrivialization_isLinearMap (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap 𝕜
      (fun v : E b ↦ (g.orthonormalizeTrivialization e (TotalSpace.mk' F b v)).2) :=
  (exists_orthonormalization g e).choose_spec.2.1 b hb

/-- The Euclidean coordinate pairing equals the supplied fiber metric. -/
theorem orthonormalizeTrivialization_inner (g : ContinuousHermitianMetric 𝕜 F E)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] {b : B} (hb : b ∈ e.baseSet)
    (v w : E b) :
    Inner.inner 𝕜 (g.orthonormalizeTrivialization e (TotalSpace.mk' F b v)).2
      (g.orthonormalizeTrivialization e (TotalSpace.mk' F b w)).2 = g.inner b v w :=
  (exists_orthonormalization g e).choose_spec.2.2 b hb v w

/-- Every point has a chart with linear Euclidean coordinates preserving the supplied metric.
This is the local orthogonal-frame refinement of the ingredient in Hatcher's proof of
Proposition 1.3, not an adapted-frame or subbundle-decomposition assertion. -/
theorem exists_orthonormalTrivialization (g : ContinuousHermitianMetric 𝕜 F E) (b₀ : B) :
    ∃ c : Trivialization (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) (π F E),
      b₀ ∈ c.baseSet ∧
      (∀ b ∈ c.baseSet,
        IsLinearMap 𝕜 (fun v : E b ↦ (c (TotalSpace.mk' F b v)).2)) ∧
      ∀ b ∈ c.baseSet, ∀ v w : E b,
        Inner.inner 𝕜 (c (TotalSpace.mk' F b v)).2 (c (TotalSpace.mk' F b w)).2 =
          g.inner b v w := by
  let e := trivializationAt F E b₀
  refine ⟨g.orthonormalizeTrivialization e, ?_, ?_, ?_⟩
  · simpa only [orthonormalizeTrivialization_baseSet] using
      FiberBundle.mem_baseSet_trivializationAt' b₀
  · intro b hb
    exact g.orthonormalizeTrivialization_isLinearMap e
      (by simpa only [orthonormalizeTrivialization_baseSet] using hb)
  · intro b hb v w
    exact g.orthonormalizeTrivialization_inner e
      (by simpa only [orthonormalizeTrivialization_baseSet] using hb) v w

end Bundle.ContinuousHermitianMetric
