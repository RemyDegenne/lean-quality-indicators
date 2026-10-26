/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Submodule closure and density of integer spans

The topological closure of a submodule `N` is the infimum of `N ⊔ U i` over
those submodules `U i` selected by a neighborhood basis at zero. The basis may
have a `Sort`-valued index type and a predicate selecting its active indices.

The closure theorem concerns a topological additive group over a semiring, with
continuous multiplication by each fixed scalar. There is no topology on the scalar semiring,
no joint scalar continuity assumption, and no Hausdorffness assumption. This is
a result about an existing group topology; it does not construct a topology from
an arbitrary filtration by semiring submodules.

For a ring whose integer casts have dense range, the integer span of any unit is
dense. This uses only continuity of multiplication by each fixed element of the
ring; commutativity, a scalar topology and joint multiplication continuity are
not required.

## Implementation notes

The proof reuses Mathlib's `Filter.HasBasis.iInter_add_right_eq_closure`, together
with `Submodule.topologicalClosure_coe`, `Submodule.coe_sup` and
`Submodule.coe_iInf`. Reindexing along `PLift.down` permits a `Sort`-valued basis
without restricting the index universe. The density result transports the dense
integer casts through the homeomorphism given by multiplication by a unit.
Centrality of integer casts identifies its range with the singleton integer span.
No new topology or instance is introduced.

## References

* Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
  (2017), Proposition 7.1.6 and Exercise 0.7.1: closure as the intersection of
  sums for a filtered module.
  The theorem here generalizes that filtered ring-module statement to any
  submodule neighborhood basis in a given topological additive group over a semiring.
* Mathlib's submodule, set-level closure and continuous-action APIs.
-/

@[expose] public section

open Filter Topology

universe u v w

namespace Submodule

section Closure

variable {R : Type u} {M : Type v} {ι : Sort w}
  [Semiring R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The closure of `N` is the infimum of its sums with the active submodules in a
basis of neighborhoods of zero. For a filtered ring module, this specializes to
Fujiwara–Kato, *Foundations of Rigid Geometry I* (2017), Proposition 7.1.6 and
Exercise 0.7.1.
The semiring formulation assumes a topological additive group and fixed-scalar
continuity; it does not construct a group topology from an arbitrary filtration. -/
theorem topologicalClosure_eq_iInf_sup
    (N : Submodule R M) {p : ι → Prop} {U : ι → Submodule R M}
    (hU : (𝓝 (0 : M)).HasBasis p (fun i ↦ (U i : Set M))) :
    N.topologicalClosure = ⨅ i, ⨅ (_ : p i), N ⊔ U i := by
  have hU' : (𝓝 (0 : M)).HasBasis (fun i : PLift ι ↦ p i.down)
      (fun i ↦ (U i.down : Set M)) :=
    hU.comp_surjective PLift.down_surjective
  apply SetLike.coe_injective
  simp only [topologicalClosure_coe, coe_iInf]
  rw [← Set.iInter_plift_down
    (fun i : ι ↦ ⋂ (_ : p i), ((N ⊔ U i : Submodule R M) : Set M))]
  simpa only [coe_sup] using
    (hU'.iInter_add_right_eq_closure (s := (N : Set M))).symm

end Closure

/-- If integer casts have dense range in a ring, the integer span of a unit is dense.
Only continuity of multiplication by each fixed ring element is needed; the ring
need not be commutative. Multiplication by the unit transports the dense integer
casts, and centrality of integer casts identifies the resulting range with the span. -/
theorem dense_int_span_of_isUnit_of_denseRange_intCast
    {R : Type u} [Ring R] [TopologicalSpace R] [ContinuousConstSMul R R]
    (hℤ : DenseRange (Int.cast : ℤ → R)) {x : R} (hx : IsUnit x) :
    Dense (Submodule.span ℤ {x} : Set R) := by
  have hmul : IsHomeomorph (fun y : R ↦ x • y) := hx.isHomeomorph_smul
  have hDense : DenseRange (fun z : ℤ ↦ x • (z : R)) :=
    hmul.surjective.denseRange.comp hℤ hmul.continuous
  rw [Submodule.span_singleton_eq_range ℤ x]
  simpa only [DenseRange, smul_eq_mul, zsmul_eq_mul'] using hDense

end Submodule
