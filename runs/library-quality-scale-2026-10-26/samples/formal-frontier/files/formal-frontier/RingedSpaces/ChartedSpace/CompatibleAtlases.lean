/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Compatible atlases on one topological space

Mixed transitions compare two *specified* charted-space structures on the same carrier and
topology. In particular, neither structure is assumed to have its own structure groupoid.
The smooth identity comparison uses the same model with corners in both directions.

## References

* Mathlib, `Mathlib/Geometry/Manifold/StructureGroupoid.lean` and
  `Mathlib/Geometry/Manifold/ChartedSpace.lean` (Sébastien Gouëzel):
  structure-groupoid compatibility and the maximal-atlas formalization.
* Mathlib, `Mathlib/Geometry/Manifold/Diffeomorph.lean` (Nicolò Cavalleri and
  Yury Kudryashov): the diffeomorphism structure, differentiability fields and
  inverse API used for the identity comparison.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for comparing local models,
  not a proof of mixed compatibility or maximal-atlas equality for two
  explicitly specified atlases, nor a comparison with an arbitrary sheaf.
-/

@[expose] public section

open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {H : Type u} [TopologicalSpace H] {M : Type v} [TopologicalSpace M]

private theorem compatible_atlases_subset_maximalAtlas (G : StructureGroupoid H)
    (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas, e.symm ≫ₕ f ∈ G) :
    (∀ e ∈ C₀.atlas, e ∈ @StructureGroupoid.maximalAtlas H M _ _ C₁ G) ∧
      (∀ f ∈ C₁.atlas, f ∈ @StructureGroupoid.maximalAtlas H M _ _ C₀ G) := by
  constructor
  · intro e he f hf
    refine ⟨h e he f hf, ?_⟩
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using
      G.symm (h e he f hf)
  · intro f hf e he
    refine ⟨?_, h e he f hf⟩
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using
      G.symm (h e he f hf)

/-- All changes of coordinates from the atlas of `C₀` to the atlas of `C₁` belong to `G`.
The reverse direction follows from symmetry of `G`; the two charted spaces share a topology. -/
theorem hasGroupoid_of_compatible_atlases (G : StructureGroupoid H)
    (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas, e.symm ≫ₕ f ∈ G) :
    @HasGroupoid H _ M _ C₀ G ∧ @HasGroupoid H _ M _ C₁ G := by
  obtain ⟨h₀, h₁⟩ := compatible_atlases_subset_maximalAtlas G C₀ C₁ h
  constructor
  · refine @HasGroupoid.mk H _ M _ C₀ G ?_
    intro e e' he he'
    let : ChartedSpace H M := C₁
    exact G.compatible_of_mem_maximalAtlas (h₀ _ he) (h₀ _ he')
  · refine @HasGroupoid.mk H _ M _ C₁ G ?_
    intro f f' hf hf'
    let : ChartedSpace H M := C₀
    exact G.compatible_of_mem_maximalAtlas (h₁ _ hf) (h₁ _ hf')

/-- Mixed compatibility identifies the maximal atlases without identifying the preferred
charts or assuming either atlas is already `G`-regular. -/
theorem maximalAtlas_eq_of_compatible_atlases (G : StructureGroupoid H)
    (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas, e.symm ≫ₕ f ∈ G) :
    @StructureGroupoid.maximalAtlas H M _ _ C₀ G =
      @StructureGroupoid.maximalAtlas H M _ _ C₁ G := by
  obtain ⟨h₀, h₁⟩ := compatible_atlases_subset_maximalAtlas G C₀ C₁ h
  apply Set.ext
  intro e
  constructor
  · intro he f hf
    let : ChartedSpace H M := C₀
    exact ⟨G.compatible_of_mem_maximalAtlas he (h₁ f hf),
      G.compatible_of_mem_maximalAtlas (h₁ f hf) he⟩
  · intro he f hf
    let : ChartedSpace H M := C₁
    exact ⟨G.compatible_of_mem_maximalAtlas he (h₀ f hf),
      G.compatible_of_mem_maximalAtlas (h₀ f hf) he⟩

variable {𝕜 : Type w} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- Mixed `C^n` transitions give manifold regularity for both specified structures. -/
theorem isManifold_of_compatible_atlases (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid n I) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ C₀ ∧
      @IsManifold 𝕜 _ E _ _ H _ I n M _ C₁ := by
  obtain ⟨h₀, h₁⟩ := hasGroupoid_of_compatible_atlases (contDiffGroupoid n I) C₀ C₁ h
  constructor
  · let : ChartedSpace H M := C₀
    let : HasGroupoid M (contDiffGroupoid n I) := h₀
    exact IsManifold.mk' I n M
  · let : ChartedSpace H M := C₁
    let : HasGroupoid M (contDiffGroupoid n I) := h₁
    exact IsManifold.mk' I n M

/-- Transport an entire atlas, including charts beyond the preferred ones, to the canonical
copy of its topological carrier. The points are unchanged under `ULift.down`.

Unlike `Homeomorph.chartedSpace`, which uses `IsLocalHomeomorph.chartedSpaceOfRightInverse`
and transports preferred charts, this construction also transports every additional atlas
member. The two charted-space structures need not be equal. -/
@[instance_reducible]
def liftedChartedSpace (C : ChartedSpace H M) : ChartedSpace H (ULift.{v} M) where
  atlas := {e | ∃ f ∈ C.atlas,
    e = (Homeomorph.ulift : ULift.{v} M ≃ₜ M).toOpenPartialHomeomorph ≫ₕ f}
  chartAt x := (Homeomorph.ulift : ULift.{v} M ≃ₜ M).toOpenPartialHomeomorph ≫ₕ
    C.chartAt x.down
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by simp, ?_⟩
    change x.down ∈ (C.chartAt x.down).source
    exact C.mem_chart_source x.down
  chart_mem_atlas x := ⟨C.chartAt x.down, C.chart_mem_atlas x.down, rfl⟩

/-- A chart belongs to the copied atlas precisely when it comes from an original chart. -/
theorem mem_liftedChartedSpace_atlas_iff (C : ChartedSpace H M)
    (e : OpenPartialHomeomorph (ULift.{v} M) H) :
    e ∈ (liftedChartedSpace C).atlas ↔ ∃ f ∈ C.atlas,
      e = (Homeomorph.ulift : ULift.{v} M ≃ₜ M).toOpenPartialHomeomorph ≫ₕ f :=
  Iff.rfl

@[simp]
theorem liftedChartedSpace_chartAt (C : ChartedSpace H M) (x : ULift.{v} M) :
    @chartAt H _ (ULift.{v} M) _ (liftedChartedSpace C) x =
      (Homeomorph.ulift : ULift.{v} M ≃ₜ M).toOpenPartialHomeomorph ≫ₕ C.chartAt x.down :=
  rfl

@[simp]
theorem liftedChartedSpace_chartAt_apply (C : ChartedSpace H M) (x y : M) :
    (@chartAt H _ (ULift.{v} M) _ (liftedChartedSpace C) (ULift.up x)) (ULift.up y) =
      C.chartAt x y := by
  simp [liftedChartedSpace_chartAt, Homeomorph.ulift]

/-- The identity on the underlying topological carrier, regarded as a `C^n` diffeomorphism
from the first charted space to the canonical copy of the second. -/
def identityDiffeomorph (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid n I) :
    @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I M _ C₀
      (ULift.{v} M) _ (liftedChartedSpace C₁) n := by
  letI := C₀
  letI := liftedChartedSpace C₁
  exact {
    toEquiv := Equiv.ulift.symm
    contMDiff_toFun := by
      intro x
      rw [contMDiffAt_iff]
      refine ⟨(Homeomorph.ulift : ULift.{v} M ≃ₜ M).symm.continuous.continuousAt, ?_⟩
      have htrans : ContDiffWithinAt 𝕜 n
          (I.extendCoordChange (C₀.chartAt x) (C₁.chartAt x)) (Set.range I)
          ((C₀.chartAt x).extend I x) := by
        let : ChartedSpace H M := C₁
        let : HasGroupoid M (contDiffGroupoid n I) :=
          (hasGroupoid_of_compatible_atlases (contDiffGroupoid n I) C₀ C₁ h).2
        have he := (compatible_atlases_subset_maximalAtlas
          (contDiffGroupoid n I) C₀ C₁ h).1 (C₀.chartAt x) (C₀.chart_mem_atlas x)
        have hf := (contDiffGroupoid n I).subset_maximalAtlas (C₁.chart_mem_atlas x)
        exact I.contDiffWithinAt_extendCoordChange' he hf
          (C₀.mem_chart_source x) (C₁.mem_chart_source x)
      change ContDiffWithinAt 𝕜 n
        (I.extendCoordChange (C₀.chartAt x) (C₁.chartAt x)) (Set.range I)
        ((C₀.chartAt x).extend I x)
      exact htrans
    contMDiff_invFun := by
      intro ⟨x⟩
      rw [contMDiffAt_iff]
      refine ⟨(Homeomorph.ulift : ULift.{v} M ≃ₜ M).continuous.continuousAt, ?_⟩
      have htrans : ContDiffWithinAt 𝕜 n
          (I.extendCoordChange (C₁.chartAt x) (C₀.chartAt x)) (Set.range I)
          ((C₁.chartAt x).extend I x) := by
        let : ChartedSpace H M := C₀
        let : HasGroupoid M (contDiffGroupoid n I) :=
          (hasGroupoid_of_compatible_atlases (contDiffGroupoid n I) C₀ C₁ h).1
        have he := (compatible_atlases_subset_maximalAtlas
          (contDiffGroupoid n I) C₀ C₁ h).2 (C₁.chartAt x) (C₁.chart_mem_atlas x)
        have hf := (contDiffGroupoid n I).subset_maximalAtlas (C₀.chart_mem_atlas x)
        exact I.contDiffWithinAt_extendCoordChange' he hf
          (C₁.mem_chart_source x) (C₀.mem_chart_source x)
      change ContDiffWithinAt 𝕜 n
        (I.extendCoordChange (C₁.chartAt x) (C₀.chartAt x)) (Set.range I)
        ((C₁.chartAt x).extend I x)
      exact htrans }

@[simp]
theorem identityDiffeomorph_apply (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid n I) (x : M) :
    identityDiffeomorph I n C₀ C₁ h x = ULift.up x :=
  rfl

@[simp]
theorem identityDiffeomorph_apply_down (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid n I) (x : ULift.{v} M) :
    identityDiffeomorph I n C₀ C₁ h x.down = x := by
  cases x
  rfl

@[simp]
theorem identityDiffeomorph_symm_apply (C₀ C₁ : ChartedSpace H M)
    (h : ∀ e ∈ C₀.atlas, ∀ f ∈ C₁.atlas,
      e.symm ≫ₕ f ∈ contDiffGroupoid n I) (x : ULift.{v} M) :
    (@Diffeomorph.symm 𝕜 _ E _ _ E _ _ H _ H _ I I M _ C₀
      (ULift.{v} M) _ (liftedChartedSpace C₁) n
      (identityDiffeomorph I n C₀ C₁ h)) x = x.down :=
  rfl

end ChartedSpace
