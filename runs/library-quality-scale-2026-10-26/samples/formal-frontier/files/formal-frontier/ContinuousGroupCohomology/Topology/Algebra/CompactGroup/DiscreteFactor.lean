/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Topology.ContinuousMap.CompactDiscrete
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Discrete-valued maps on compact groups factor through finite quotients

An arbitrary continuous map from a compact topological group to a discrete space
descends through an open normal subgroup. Neither the map nor its target needs an
algebraic structure; the group need not be Hausdorff or totally disconnected.
-/

public section

namespace ContinuousMap

universe u v

variable {G : Type u} {Y : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace Y] [DiscreteTopology Y]

/-- A discrete-valued continuous map on a compact group factors through a finite,
discrete quotient by an open normal subgroup. The equality is pointwise at the
canonical quotient map; no homomorphism hypothesis is placed on the map. -/
theorem exists_openNormalSubgroup_factor (f : C(G, Y)) :
    ∃ (N : OpenNormalSubgroup G) (fbar : C(G ⧸ N.toSubgroup, Y)),
      ∀ g : G, fbar (QuotientGroup.mk g) = f g := by
  have discrete_maps : DiscreteTopology C(G, Y) := discreteTopology_of_compactSpace
  let shift : G → C(G, Y) := fun h =>
    ⟨fun g => f (g * h), f.continuous.comp (continuous_id.mul continuous_const)⟩
  have shift_continuous : Continuous shift := by
    apply continuous_of_continuous_uncurry
    exact f.continuous.comp (continuous_snd.mul continuous_fst)
  let W : Set G := {h | shift h = f}
  have W_clopen : IsClopen W :=
    ⟨((discreteTopology_iff_forall_isClosed.mp discrete_maps) {f}).preimage shift_continuous,
      ((discreteTopology_iff_forall_isOpen.mp discrete_maps) {f}).preimage shift_continuous⟩
  have one_mem : (1 : G) ∈ W := by
    change shift 1 = f
    ext g
    simp [shift]
  obtain ⟨N, hN⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one W_clopen one_mem
  have respects (a b : G) (hab : QuotientGroup.leftRel N.toSubgroup a b) : f a = f b := by
    have hshift : shift (a⁻¹ * b) = f := hN ((QuotientGroup.leftRel_apply).mp hab)
    have hpoint := congrArg (fun k : C(G, Y) => k a) hshift
    change f (a * (a⁻¹ * b)) = f a at hpoint
    simpa only [mul_inv_cancel_left] using hpoint.symm
  let fbar : C(G ⧸ N.toSubgroup, Y) :=
    ⟨Quotient.lift f respects, f.continuous.quotient_lift respects⟩
  exact ⟨N, fbar, fun _ => rfl⟩

end ContinuousMap
