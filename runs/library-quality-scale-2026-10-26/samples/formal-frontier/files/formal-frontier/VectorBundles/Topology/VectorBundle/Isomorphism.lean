/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import VectorBundles.Topology.VectorBundle.CoordinateMap
public import VectorBundles.Analysis.Normed.Ring.Units

/-!
# Homeomorphisms from fiberwise linear equivalences

A family of algebraic linear equivalences between two vector bundles over the same base induces a
homeomorphism of total spaces as soon as its forward total-space map is continuous, provided the
source model is finite dimensional over a nontrivially normed field and the target model has the
module topology. In particular, this holds over a complete nontrivially normed field.

The resulting `Homeomorph` preserves the base point and restricts to the supplied linear equivalence
on each fiber. No separate structure for bundle isomorphisms is introduced.

## Implementation notes

Only the source model is assumed finite dimensional: at each base point the two trivializations and
the given fiber equivalence identify the target model with the source model. No nonemptiness or
separation hypothesis on the base is required, and zero-dimensional fibers are permitted.
At an actual point of the target total space, forward continuity and the target module topology
also give the source model its module topology. Coordinate operators are normalized into units of
the source endomorphism ring, where inversion is continuous without completeness. All operators
use the original model norms. Completeness of the scalar field is needed only to recover the
module-topology hypothesis for arbitrary finite-dimensional normed models.

The coordinate and module-topology arguments use Mathlib's vector-bundle APIs by Nicolò Cavalleri,
Sébastien Gouëzel, Heather Macbeth, Patrick Massot and Floris van Doorn, and its module-topology API
by Kevin Buzzard and Will Sawin. The unit argument uses the topology of units developed in Mathlib.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, Lemma 1.1, printed p. 8.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

@[expose] public section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂

open Bundle

namespace VectorBundle

/-- The inverse total-space map of a continuous family of fiberwise algebraic linear equivalences
is continuous when the source model is finite dimensional and the given target model has the
module topology. No scalar completeness or source module-topology hypothesis is imposed.

This generalizes the inverse-continuity assertion in Hatcher, *Vector Bundles and K-Theory*,
Lemma 1.1. The model norms, fiber topologies and bundle dictionaries are unchanged. -/
theorem continuous_totalSpace_symm_of_isModuleTopology
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {B : Type uB} [TopologicalSpace B]
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [FiniteDimensional 𝕜 F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [IsModuleTopology 𝕜 F₂]
    {E₁ : B → Type uE₁} {E₂ : B → Type uE₂}
    [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
    [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
    [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    Continuous (fun p : TotalSpace F₂ E₂ =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace F₁ E₁)) := by
  classical
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  let c₁ := trivializationAt F₁ E₁ p₀.proj
  let c₂ := trivializationAt F₂ E₂ p₀.proj
  have hb₁ : p₀.proj ∈ c₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
  have hb₂ : p₀.proj ∈ c₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
  have hU₁ := c₁.open_baseSet.mem_nhds hb₁
  have hU₂ := c₂.open_baseSet.mem_nhds hb₂
  let aₗ (b : B) (h₁ : b ∈ c₁.baseSet) (h₂ : b ∈ c₂.baseSet) : F₁ ≃ₗ[𝕜] F₂ :=
    (((c₁.linearEquivAt 𝕜 b h₁).symm.trans (e b)).trans
      (c₂.linearEquivAt 𝕜 b h₂))
  -- Continuity of one fixed model map follows directly from joint coordinate evaluation.
  -- This step does not use the module topology on the source.
  have ha₀ : Continuous (aₗ p₀.proj hb₁ hb₂) := by
    have h := (c₁.continuousOn_linearMapAt_comp_apply c₂
      (fun b => (e b).toLinearMap) htotal).comp_continuous
        (Continuous.prodMk_right p₀.proj)
        (fun v : F₁ => ⟨⟨hb₁, hb₂⟩, Set.mem_univ v⟩)
    refine h.congr fun v => ?_
    change c₂.linearMapAt 𝕜 p₀.proj (e p₀.proj (c₁.symmₗ 𝕜 p₀.proj v)) =
      (c₂.linearEquivAt 𝕜 p₀.proj hb₂)
        (e p₀.proj ((c₁.linearEquivAt 𝕜 p₀.proj hb₁).symm v))
    rw [c₂.coe_linearMapAt_of_mem (R := 𝕜) hb₂, c₁.symmₗ_apply hb₁,
      c₂.linearEquivAt_apply, c₁.linearEquivAt_symm_apply]
  let a₀ : F₁ ≃L[𝕜] F₂ :=
    { toLinearEquiv := aₗ p₀.proj hb₁ hb₂
      continuous_toFun := ha₀
      continuous_invFun := IsModuleTopology.continuous_of_linearMap
        (aₗ p₀.proj hb₁ hb₂).symm.toLinearMap }
  -- Only this fixed inverse is used to transport the source module-topology class.
  let : IsModuleTopology 𝕜 F₁ := IsModuleTopology.iso a₀.symm
  let A : B → F₁ →L[𝕜] F₂ := fun b =>
    ⟨(c₂.linearMapAt 𝕜 b).comp ((e b).toLinearMap.comp (c₁.symmₗ 𝕜 b)),
      IsModuleTopology.continuous_of_linearMap _⟩
  let a (b : B) (h₁ : b ∈ c₁.baseSet) (h₂ : b ∈ c₂.baseSet) : F₁ ≃L[𝕜] F₂ :=
    { toLinearEquiv := aₗ b h₁ h₂
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (aₗ b h₁ h₂).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap
        (aₗ b h₁ h₂).symm.toLinearMap }
  have hAa (b : B) (h₁ : b ∈ c₁.baseSet) (h₂ : b ∈ c₂.baseSet) :
      A b = (a b h₁ h₂ : F₁ →L[𝕜] F₂) := by
    ext v
    simp [A, a, aₗ, h₁, h₂]
  have hA : ContinuousAt A p₀.proj :=
    (c₁.continuousOn_linearMapAt_comp_of_isModuleTopology c₂
      (fun b => (e b).toLinearMap) htotal).continuousAt (Filter.inter_mem hU₁ hU₂)
  -- Normalize by the fixed equivalence, obtaining existing units of End(F₁).
  -- Their definition outside the overlap is irrelevant to continuity at the chosen point.
  let u : B → (F₁ →L[𝕜] F₁)ˣ := fun b =>
    if hb : b ∈ c₁.baseSet ∩ c₂.baseSet then
      ((a b hb.1 hb.2).trans a₀.symm).toUnit
    else 1
  have huval : ContinuousAt (fun b => (u b : F₁ →L[𝕜] F₁)) p₀.proj := by
    have hnorm : ContinuousAt (fun b => (a₀.symm : F₂ →L[𝕜] F₁).comp (A b))
        p₀.proj := continuousAt_const.clm_comp hA
    apply hnorm.congr_of_eventuallyEq
    filter_upwards [hU₁, hU₂] with b h₁ h₂
    rw [hAa b h₁ h₂]
    ext v
    exact congrArg (fun w : (F₁ →L[𝕜] F₁)ˣ => w.val v)
      (show u b = ((a b h₁ h₂).trans a₀.symm).toUnit from
        dite_eq_left (show b ∈ c₁.baseSet ∩ c₂.baseSet from ⟨h₁, h₂⟩))
  have hu : ContinuousAt u p₀.proj :=
    (Units.isEmbedding_val_seminormedRing (R := F₁ →L[𝕜] F₁)).isInducing.continuousAt_iff.mpr
      huval
  have hi : ContinuousAt (fun b => (↑((u b)⁻¹) : F₁ →L[𝕜] F₁)) p₀.proj :=
    Units.continuous_coe_inv.continuousAt.comp hu
  have huinv (b : B) (h₁ : b ∈ c₁.baseSet) (h₂ : b ∈ c₂.baseSet) (v : F₂) :
      (↑((u b)⁻¹) : F₁ →L[𝕜] F₁) (a₀.symm v) = (a b h₁ h₂).symm v := by
    simp only [u, dite_eq_left (show b ∈ c₁.baseSet ∩ c₂.baseSet from ⟨h₁, h₂⟩)]
    change ((a b h₁ h₂).trans a₀.symm).symm (a₀.symm v) = (a b h₁ h₂).symm v
    simp
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F₂ E₂).continuousAt, ?_⟩
  have hv : ContinuousAt (fun p : TotalSpace F₂ E₂ => a₀.symm (c₂ p).2) p₀ :=
    a₀.symm.continuous.continuousAt.comp
      (c₂.continuousAt (c₂.mem_source.mpr hb₂)).snd
  have heval := (hi.comp (FiberBundle.continuous_proj F₂ E₂).continuousAt).clm_apply hv
  apply heval.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj F₂ E₂).continuousAt.preimage_mem_nhds hU₁,
    (FiberBundle.continuous_proj F₂ E₂).continuousAt.preimage_mem_nhds hU₂] with p h₁ h₂
  change (c₁ ⟨p.proj, (e p.proj).symm p.2⟩).2 =
    (↑((u p.proj)⁻¹) : F₁ →L[𝕜] F₁) (a₀.symm (c₂ p).2)
  rw [huinv p.proj h₁ h₂]
  change (c₁ ⟨p.proj, (e p.proj).symm p.2⟩).2 =
    (c₁.linearEquivAt 𝕜 p.proj h₁)
      ((e p.proj).symm ((c₂.linearEquivAt 𝕜 p.proj h₂).symm (c₂ p).2))
  rw [c₂.linearEquivAt_symm_apply, c₂.symm_proj_apply p h₂, c₁.linearEquivAt_apply]

section CompleteField

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
  {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B → Type uE₁} {E₂ : B → Type uE₂}
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The inverse total-space map of a continuous family of fiberwise algebraic linear equivalences
is continuous when the source model is finite dimensional over a complete nontrivially normed field.

This is the inverse-continuity assertion in Hatcher, *Vector Bundles and K-Theory*, Lemma 1.1.
Continuity of the inverse family, including continuity in the base variable, is a conclusion rather
than a hypothesis. -/
theorem continuous_totalSpace_symm
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    Continuous (fun p : TotalSpace F₂ E₂ =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace F₁ E₁)) := by
  classical
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  let c₁ := trivializationAt F₁ E₁ p₀.proj
  let c₂ := trivializationAt F₂ E₂ p₀.proj
  have hb₁ : p₀.proj ∈ c₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
  have hb₂ : p₀.proj ∈ c₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
  let a₀ : F₁ ≃ₗ[𝕜] F₂ :=
    (((c₁.linearEquivAt 𝕜 p₀.proj hb₁).symm.trans (e p₀.proj)).trans
      (c₂.linearEquivAt 𝕜 p₀.proj hb₂))
  let : FiniteDimensional 𝕜 F₂ := a₀.finiteDimensional
  let : IsModuleTopology 𝕜 F₂ := isModuleTopologyOfFiniteDimensional
  exact (continuous_totalSpace_symm_of_isModuleTopology
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal).continuousAt

/-- A continuous fiberwise algebraic linear equivalence of finite-rank vector bundles over the same
base, packaged as a homeomorphism of total spaces.

The forward map acts by `e b` on the fiber over `b`, and the inverse acts by `(e b).symm`. Thus both
maps preserve the base point. This gives the bundle isomorphism of Hatcher, *Vector Bundles and
K-Theory*, Lemma 1.1, without introducing an additional bundle-isomorphism structure. -/
noncomputable def homeomorphOfFiberwiseLinearEquiv
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := congrArg (TotalSpace.mk' F₁ p.proj) ((e p.proj).symm_apply_apply p.2)
  right_inv p := congrArg (TotalSpace.mk' F₂ p.proj) ((e p.proj).apply_symm_apply p.2)
  continuous_toFun := htotal
  continuous_invFun := continuous_totalSpace_symm e htotal

variable (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
  (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
    (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂)))

/-- The total-space homeomorphism acts by the supplied linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquiv_apply (p : TotalSpace F₁ E₁) :
    homeomorphOfFiberwiseLinearEquiv e htotal p = ⟨p.proj, e p.proj p.2⟩ := rfl

/-- The inverse total-space homeomorphism acts by the inverse linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquiv_symm_apply (p : TotalSpace F₂ E₂) :
    (homeomorphOfFiberwiseLinearEquiv e htotal).symm p =
      ⟨p.proj, (e p.proj).symm p.2⟩ := rfl

/-- The forward total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquiv_apply_proj (p : TotalSpace F₁ E₁) :
    (homeomorphOfFiberwiseLinearEquiv e htotal p).proj = p.proj := rfl

/-- The inverse total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquiv_symm_apply_proj (p : TotalSpace F₂ E₂) :
    ((homeomorphOfFiberwiseLinearEquiv e htotal).symm p).proj = p.proj := rfl

end CompleteField

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
  {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [IsModuleTopology 𝕜 F₂]
  {E₁ : B → Type uE₁} {E₂ : B → Type uE₂}
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- A continuous fiberwise algebraic linear equivalence over the same base, packaged as a
homeomorphism of total spaces when the source model is finite dimensional and the given target
model has the module topology.

The maps are those of Hatcher, *Vector Bundles and K-Theory*, Lemma 1.1: the forward map acts by
`e b` on each fiber and the inverse acts by `(e b).symm`. Both preserve the base point. -/
noncomputable def homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := congrArg (TotalSpace.mk' F₁ p.proj) ((e p.proj).symm_apply_apply p.2)
  right_inv p := congrArg (TotalSpace.mk' F₂ p.proj) ((e p.proj).apply_symm_apply p.2)
  continuous_toFun := htotal
  continuous_invFun := continuous_totalSpace_symm_of_isModuleTopology
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal

variable (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
  (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
    (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂)))

/-- The total-space homeomorphism acts by the supplied linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_apply (p : TotalSpace F₁ E₁) :
    homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal p =
        ⟨p.proj, e p.proj p.2⟩ := rfl

/-- The inverse total-space homeomorphism acts by the inverse linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_symm_apply (p : TotalSpace F₂ E₂) :
    (homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal).symm p =
        ⟨p.proj, (e p.proj).symm p.2⟩ := rfl

/-- The forward total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_apply_proj (p : TotalSpace F₁ E₁) :
    (homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal p).proj =
        p.proj := rfl

/-- The inverse total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_symm_apply_proj (p : TotalSpace F₂ E₂) :
    ((homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal).symm p).proj =
        p.proj := rfl

end VectorBundle
