/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Continuity from the identity for a crossed functional equation

The functional equation `f (g * h) = ρ g (f h) + f g` propagates continuity at the identity
to continuity everywhere when left translations in the domain, right translations in the
codomain, and the fixed coefficient maps `ρ g` are continuous. The codomain only needs an
addition operation: no additive laws or action laws for `ρ` are required. All topology
assumptions concern the given operations and topologies, not joint continuity.

The specialization to `groupCohomology.IsCocycle₁` promotes an algebraic cocycle to a
continuous function. It needs only the given scalar multiplication, not action laws or a
topology on a coefficient ring. Normalization is separate:
`groupCohomology.map_one_of_isCocycle₁` requires a `MulAction` and gives `f 1 = 0`.

For ordinary homomorphisms, use `continuous_of_continuousAt_one` or its additive counterpart
`continuous_of_continuousAt_zero` under their topological-group and continuous-operation
hypotheses. In the shared commutative additive setting, the trivial-coefficient-map equation,
together with `f 1 = 0`, identifies a homomorphism `Additive G →+ A`. At the representation
endpoint with trivial action, `groupCohomology.cocycles₁IsoOfIsTrivial` is the existing bridge.
The criterion here does not generalize the ordinary theorem's full noncommutative target scope.
-/

@[expose] public section

universe v w

/-- A crossed functional equation reduces continuity to continuity at the identity.
Only fixed left translations, fixed right translations, and the fixed coefficient maps
are assumed continuous. In particular, `V` need not be an additive monoid and `ρ` need not
satisfy any action laws. -/
theorem continuous_iff_continuousAt_one_of_crossed
    {G : Type v} {V : Type w} [Group G] [TopologicalSpace G] [Add V] [TopologicalSpace V]
    (ρ : G → V → V) (f : G → V)
    (hf : ∀ g h, f (g * h) = ρ g (f h) + f g)
    (L : ∀ g : G, Continuous (fun h : G => g * h))
    (R : ∀ a : V, Continuous (fun b : V => b + a))
    (C : ∀ g : G, Continuous (fun b : V => ρ g b)) :
    Continuous f ↔ ContinuousAt f 1 := by
  constructor
  · intro h
    exact h.continuousAt
  · intro h
    rw [continuous_iff_continuousAt]
    intro g
    have h₁ : ContinuousAt (fun x : G => f (g⁻¹ * x)) g :=
      (show ContinuousAt f (g⁻¹ * g) by
        simpa only [inv_mul_cancel] using h).comp (L g⁻¹).continuousAt
    have h₂ : ContinuousAt (fun x : G => ρ g (f (g⁻¹ * x)) + f g) g :=
      (R (f g)).continuousAt.comp ((C g).continuousAt.comp h₁)
    have heq : (fun x : G => ρ g (f (g⁻¹ * x)) + f g) = f := by
      funext x
      rw [← hf g (g⁻¹ * x), ← mul_assoc, mul_inv_cancel, one_mul]
    rw [heq] at h₂
    exact h₂

/-- An algebraic one-cocycle is continuous if and only if it is continuous at the identity,
provided the fixed domain left translations, coefficient right translations, and scalar maps
are continuous. No action laws beyond the given `SMul` data are needed. -/
theorem groupCohomology.IsCocycle₁.continuous_iff_continuousAt_one
    {G : Type v} {A : Type w} [Group G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A] {f : G → A}
    (hf : groupCohomology.IsCocycle₁ f)
    (L : ∀ g : G, Continuous (fun h : G => g * h))
    (R : ∀ a : A, Continuous (fun b : A => b + a))
    (C : ∀ g : G, Continuous (fun a : A => g • a)) :
    Continuous f ↔ ContinuousAt f 1 :=
  continuous_iff_continuousAt_one_of_crossed (fun g a => g • a) f hf L R C
