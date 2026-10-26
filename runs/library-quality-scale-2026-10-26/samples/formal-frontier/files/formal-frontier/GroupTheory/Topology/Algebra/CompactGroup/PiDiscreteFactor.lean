/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.CompactGroup.DiscreteFactor
public import GroupTheory.Topology.Algebra.OpenSubgroup.Pi
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Finite-coordinate quotient factorization on compact group powers

A continuous map from an arbitrary power of a compact topological group to a
discrete space factors through finitely many coordinates and one open normal
subgroup of the factor group. The descended map has domain `s → G ⧸ N.toSubgroup`
for a finite set `s` of coordinates. This domain is finite and discrete, even
when the original index type is infinite. The finite set may be empty.

The observer need not be a homomorphism, its target needs no algebraic structure,
and the group need not be Hausdorff or totally disconnected. The topologies are
the canonical product and group-quotient topologies. An infinite power of a
nontrivial finite quotient is not itself a finite discrete domain.

The factorization combines compact-group factorization with finite-cylinder
containment. Coordinate restriction and extension by the identity are continuous
product constructions. Descent along the coordinatewise open quotient map is
provided by `Topology.IsQuotientMap.lift`, characterized by `lift_comp` and
`liftEquiv`.

## References

- Formal Frontier Agents, *Continuous Group Cohomology*, compact-group/discrete-map
  factorization formalization, reused through
  `ContinuousMap.exists_openNormalSubgroup_factor` in
  `GroupTheory.Topology.Algebra.CompactGroup.DiscreteFactor`.
- Mathlib, `Mathlib.Topology.Algebra.OpenSubgroup` and
  `Mathlib.Topology.Algebra.Group.Quotient`, for finite discrete open-subgroup
  quotients and their open quotient maps.
- Mathlib, `Mathlib.Topology.Constructions` and
  `Mathlib.Topology.ContinuousMap.Basic`, for products of open quotient maps,
  `ContinuousMap.pi`, `ContinuousMap.piMap`, and continuous quotient descent.
-/

@[expose] public section

namespace ContinuousMap

universe uI uG uY

variable {I : Type uI} {G : Type uG} {Y : Type uY}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace Y] [DiscreteTopology Y]

/-- A discrete-valued continuous map on an arbitrary compact group power factors
through the quotients of finitely many coordinates by one open normal subgroup
of the factor group. The descended domain is finite and discrete, and the
factorization equation uses the canonical coordinatewise quotient map. -/
theorem exists_finset_openNormalSubgroup_pi_factor (f : C(I → G, Y)) :
    ∃ (s : Finset I) (N : OpenNormalSubgroup G)
      (fbar : C((s → (G ⧸ N.toSubgroup)), Y)),
      ∀ x : I → G,
        fbar (fun i : s => QuotientGroup.mk (x i)) = f x := by
  classical
  obtain ⟨M, fM, hfM⟩ := f.exists_openNormalSubgroup_factor
  obtain ⟨s, N, hN⟩ := M.exists_finset_uniform_pi_subset
  -- Equality on the selected quotient coordinates implies equality modulo M.
  have same_value (x y : I → G)
      (hxy : ∀ i : s, (QuotientGroup.mk (x i) : G ⧸ N.toSubgroup) =
        QuotientGroup.mk (y i)) : f x = f y := by
    have hmem : x⁻¹ * y ∈ M := hN _ fun i => QuotientGroup.eq.mp (hxy i)
    have hquot : (QuotientGroup.mk x : (I → G) ⧸ M.toSubgroup) =
        QuotientGroup.mk y := QuotientGroup.eq.mpr hmem
    calc
      f x = fM (QuotientGroup.mk x) := (hfM x).symm
      _ = fM (QuotientGroup.mk y) := congrArg fM hquot
      _ = f y := hfM y
  let restrict : C(I → G, s → G) :=
    ContinuousMap.precomp (fun i : s => (i : I))
  let extend : C(s → G, I → G) := ContinuousMap.pi fun i =>
    if hi : i ∈ s then ContinuousMap.eval (⟨i, hi⟩ : s)
    else ContinuousMap.const (s → G) (1 : G)
  have extend_apply (a : s → G) (i : s) : extend a i = a i := by
    simp [extend, i.property]
  let q : C(s → G, s → (G ⧸ N.toSubgroup)) :=
    ContinuousMap.piMap fun _ : s =>
      ⟨QuotientGroup.mk, QuotientGroup.continuous_mk⟩
  have hq : Topology.IsQuotientMap q :=
    (IsOpenQuotientMap.piMap fun _ : s =>
      (QuotientGroup.isOpenQuotientMap_mk :
        IsOpenQuotientMap (QuotientGroup.mk : G → G ⧸ N.toSubgroup))).isQuotientMap
  have respects : Function.FactorsThrough (f.comp extend) q := by
    intro a b hab
    apply same_value (extend a) (extend b)
    intro i
    have hi := congrArg (fun z : s → (G ⧸ N.toSubgroup) => z i) hab
    change (QuotientGroup.mk (a i) : G ⧸ N.toSubgroup) =
      QuotientGroup.mk (b i) at hi
    simpa only [extend_apply] using hi
  let fbar : C(s → (G ⧸ N.toSubgroup), Y) := hq.lift (f.comp extend) respects
  have triangle (a : s → G) : fbar (q a) = f (extend a) :=
    congrArg (fun k : C(s → G, Y) => k a) (hq.lift_comp (f.comp extend) respects)
  refine ⟨s, N, fbar, ?_⟩
  intro x
  calc
    fbar (fun i : s => QuotientGroup.mk (x i)) = fbar (q (restrict x)) := rfl
    _ = f (extend (restrict x)) := triangle (restrict x)
    _ = f x := same_value _ _ fun i => by
      rw [extend_apply]
      rfl

end ContinuousMap
