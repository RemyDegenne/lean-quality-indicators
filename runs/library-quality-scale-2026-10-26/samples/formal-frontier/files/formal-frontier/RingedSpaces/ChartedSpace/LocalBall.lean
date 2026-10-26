/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Chart coordinates on an entire open ball

At any regularity indexed by `ℕ∞ω`, a chart of a boundaryless self-model manifold
restricts near a point to a diffeomorphism onto an entire positive-radius model ball.
No dimension or nonemptiness condition on the model space is required.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for entire-ball local models,
  not a proof of this indexed chart construction or arbitrary-sheaf recovery.
* Mathlib, `Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean` (Sébastien Gouëzel
  and Floris van Doorn): chart regularity used for the construction.
* Mathlib, `Mathlib/Geometry/Manifold/Diffeomorph.lean` (Nicolò Cavalleri and
  Yury Kudryashov): the diffeomorphism structure and differentiability fields
  used for the indexed coordinate diffeomorphism.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

/-- The entire open model ball centered at the chart coordinate of a point. -/
def chartBall (x : M) (radius : ℝ) : Opens E :=
  ⟨Metric.ball ((chartAt E x) x) radius, Metric.isOpen_ball⟩

@[simp] theorem mem_chartBall (x : M) (radius : ℝ) (point : E) :
    point ∈ chartBall (E := E) x radius ↔
      dist point ((chartAt E x) x) < radius :=
  Metric.mem_ball

/-- An open neighborhood with coordinates covering an entire model ball. -/
structure ChartLocalBall (n : ℕ∞ω) (x : M) where
  neighborhood : Opens M
  mem_neighborhood : x ∈ neighborhood
  neighborhood_subset_source : (neighborhood : Set M) ⊆ (chartAt E x).source
  radius : ℝ
  radius_pos : 0 < radius
  coord : neighborhood ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ chartBall (E := E) x radius
  coord_apply (point : neighborhood) :
    (coord point : E) = (chartAt E x) point.1
  coord_symm_apply (point : chartBall (E := E) x radius) :
    ((coord.symm point : neighborhood) : M) = (chartAt E x).symm point.1

attribute [simp] ChartLocalBall.coord_apply ChartLocalBall.coord_symm_apply

namespace ChartLocalBall

variable {n : ℕ∞ω} {x : M} (b : ChartLocalBall (𝕜 := 𝕜) (E := E) n x)

/-- The full ball targeted by the coordinate diffeomorphism. -/
abbrev ball : Opens E := chartBall (E := E) x b.radius

@[simp] theorem mem_ball (point : E) :
    point ∈ b.ball ↔ dist point ((chartAt E x) x) < b.radius :=
  mem_chartBall x b.radius point

@[simp] theorem center_mem_ball : (chartAt E x) x ∈ b.ball := by
  exact (b.mem_ball _).2 (by simpa using b.radius_pos)

/-- The chart center as a point of the entire coordinate ball. -/
def center : b.ball := ⟨(chartAt E x) x, b.center_mem_ball⟩

@[simp] theorem coord_at_center :
    b.coord ⟨x, b.mem_neighborhood⟩ = b.center := by
  apply Subtype.ext
  exact b.coord_apply _

end ChartLocalBall

/-- Chosen coordinates around a point at arbitrary manifold regularity. -/
def chartLocalBall (n : ℕ∞ω) [IsManifold 𝓘(𝕜, E) n M] (x : M) :
    ChartLocalBall (𝕜 := 𝕜) (E := E) n x := by
  let chart := chartAt E x
  have hexists : ∃ radius > 0, Metric.ball (chart x) radius ⊆ chart.target :=
    Metric.isOpen_iff.mp chart.open_target (chart x) (mem_chart_target E x)
  let radius := Classical.choose hexists
  have hradius : 0 < radius := (Classical.choose_spec hexists).1
  have hball : Metric.ball (chart x) radius ⊆ chart.target :=
    (Classical.choose_spec hexists).2
  let ball : Opens E := chartBall x radius
  have hball_subset : (ball : Set E) ⊆ chart.target := hball
  let neighborhood : Opens M :=
    ⟨chart.source ∩ chart ⁻¹' (ball : Set E),
      chart.isOpen_inter_preimage ball.isOpen⟩
  have hmem : x ∈ neighborhood := by
    exact ⟨mem_chart_source E x, (mem_chartBall x radius (chart x)).2
      (by simpa [chart] using hradius)⟩
  have hsource : (neighborhood : Set M) ⊆ chart.source := Set.inter_subset_left
  have himage : chart '' (neighborhood : Set M) = (ball : Set E) := by
    apply Set.Subset.antisymm
    · rintro targetPoint ⟨point, ⟨-, hballPoint⟩, rfl⟩
      exact hballPoint
    · intro targetPoint hballPoint
      have htarget : targetPoint ∈ chart.target := hball_subset hballPoint
      exact ⟨chart.symm targetPoint, ⟨chart.map_target htarget,
        by simpa only [Set.mem_preimage, chart.right_inv htarget] using hballPoint⟩,
          chart.right_inv htarget⟩
  let homeo : neighborhood ≃ₜ ball :=
    chart.homeomorphOfImageSubsetSource hsource himage
  have hsmooth : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo := by
    intro point
    have hchart : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        chart point.1 :=
      (contMDiffOn_chart (I := 𝓘(𝕜, E)) (x := x) point.1
        (hsource point.2)).contMDiffAt (chart.open_source.mem_nhds (hsource point.2))
    have hrestr : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (fun point : neighborhood => chart point.1) point :=
      contMDiffAt_subtype_iff.mpr hchart
    have htarget : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo) point := by
      convert hrestr using 1
      funext sourcePoint
      rfl
    exact (show ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo) point ↔
          ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo point from
        ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff homeo Set.univ point).mp htarget
  have hsmooth_symm : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo.symm := by
    intro point
    have hchart : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        chart.symm point.1 :=
      (contMDiffOn_chart_symm (I := 𝓘(𝕜, E)) (x := x) point.1
        (hball_subset point.2)).contMDiffAt
          (chart.open_target.mem_nhds (hball_subset point.2))
    have hrestr : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (fun point : ball => chart.symm point.1) point :=
      contMDiffAt_subtype_iff.mpr hchart
    have htarget : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo.symm) point := by
      convert hrestr using 1
      funext targetPoint
      rfl
    exact (show ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo.symm) point ↔
          ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo.symm point from
        ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff homeo.symm Set.univ point).mp htarget
  exact {
    neighborhood := neighborhood
    mem_neighborhood := hmem
    neighborhood_subset_source := hsource
    radius := radius
    radius_pos := hradius
    coord := { toEquiv := homeo.toEquiv
               contMDiff_toFun := hsmooth
               contMDiff_invFun := hsmooth_symm }
    coord_apply := fun point => rfl
    coord_symm_apply := fun point => rfl }

end ChartedSpace
