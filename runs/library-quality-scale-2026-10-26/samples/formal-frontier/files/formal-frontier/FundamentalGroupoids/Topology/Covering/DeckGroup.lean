/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Covering.Deck
public import Mathlib.Topology.Covering.Quotient

/-!
# Deck transformations on fibers

The deck transformation group of a map acts on each of its point fibers. For a
separated, locally injective map with preconnected total space, evaluation at a
specified point embeds the deck group into the fiber containing that point.
Consequently, a deck transformation fixing a point is the identity. In particular,
this holds for a covering map with preconnected total space.

## Implementation notes

The fiber action needs only a topology on the total space. The evaluation
embedding and fixed-point statements require neither a topology on the codomain
nor a Hausdorff total space. The specified point supplies nonemptiness; no global
connectedness or nonemptiness instance is assumed for the action. Evaluation is
not asserted to be surjective.

For a quotient covering by the deck group, the fiber action agrees with
`IsQuotientCoveringMap.mulActionFiber`. That construction requires the
quotient-covering hypotheses, including transitivity on each fiber and disjoint
translates of neighborhoods, which are not imposed on an arbitrary map here.

Deck transformations here are self-homeomorphisms commuting with the map. The
covering-map fixed-point statement specializes uniqueness of maps of covers by
comparing a deck transformation with the identity.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, p. 29,
  for uniqueness of maps of covers.
* Mathlib's deck transformation group, formalized by Kim Morrison in
  `Mathlib.Topology.Covering.Deck`.
* Mathlib's uniqueness theorem `IsSeparatedMap.eq_of_comp_eq`, formalized by
  Junyan Xu in `Mathlib.Topology.SeparatedMap`.

The fiber action uses Mathlib's restriction of an action to an invariant subset,
`SubMulAction.mulAction`.
-/

@[expose] public section

universe u v

namespace deck

variable {E : Type u} {B : Type v} [TopologicalSpace E] {p : E → B}

/-- Deck transformations act on every point fiber by their action on the total space. -/
instance instMulActionFiber (p : E → B) (b : B) : MulAction (deck p) (p ⁻¹' {b}) :=
  SubMulAction.mulAction ⟨p ⁻¹' {b}, fun g e he ↦ (proj_smul g e).trans he⟩

/-- The action on a fiber is the restriction of the action on the total space. -/
@[simp]
theorem coe_fiber_smul {b : B} (g : deck p) (e : p ⁻¹' {b}) :
    ((g • e : p ⁻¹' {b}) : E) = g • (e : E) :=
  rfl

section Preconnected

/-- Evaluation embeds the deck group of a separated, locally injective map into the
fiber containing a specified point, provided the total space is preconnected.
The injectivity is the deck-transformation specialization of Mathlib's
`IsSeparatedMap.eq_of_comp_eq`. -/
def evalEmbedding [PreconnectedSpace E] (hsep : IsSeparatedMap p)
    (hinj : IsLocallyInjective p) (e : E) :
    deck p ↪ p ⁻¹' {p e} where
  toFun g := ⟨g • e, proj_smul g e⟩
  inj' := by
    intro g h hgh
    apply Subtype.ext
    apply DFunLike.coe_injective
    exact hsep.eq_of_comp_eq hinj (g : E ≃ₜ E).continuous (h : E ≃ₜ E).continuous
      ((comp_eq g).trans (comp_eq h).symm) e (congrArg Subtype.val hgh)

/-- Evaluation into the fiber applies the deck transformation to the specified point. -/
@[simp]
theorem evalEmbedding_apply [PreconnectedSpace E] (hsep : IsSeparatedMap p)
    (hinj : IsLocallyInjective p) (e : E) (g : deck p) :
    evalEmbedding hsep hinj e g = ⟨g • e, proj_smul g e⟩ :=
  rfl

/-- Coercing an evaluated deck transformation to the total space gives its action. -/
@[simp]
theorem coe_evalEmbedding_apply [PreconnectedSpace E] (hsep : IsSeparatedMap p)
    (hinj : IsLocallyInjective p) (e : E) (g : deck p) :
    (evalEmbedding hsep hinj e g : E) = g • e :=
  rfl

/-- Evaluation intertwines multiplication in the deck group and its action on the fiber. -/
theorem evalEmbedding_mul [PreconnectedSpace E] (hsep : IsSeparatedMap p)
    (hinj : IsLocallyInjective p) (e : E) (g h : deck p) :
    evalEmbedding hsep hinj e (g * h) = g • evalEmbedding hsep hinj e h := by
  apply Subtype.ext
  exact mul_smul g h e

/-- A deck transformation of a separated, locally injective map with preconnected
total space is the identity if it fixes a point. This is the fixed-point
specialization of the lift uniqueness in Mathlib's `IsSeparatedMap.eq_of_comp_eq`. -/
theorem eq_one_of_smul_eq [PreconnectedSpace E] (hsep : IsSeparatedMap p)
    (hinj : IsLocallyInjective p)
    {g : deck p} {e : E} (he : g • e = e) : g = 1 := by
  apply (evalEmbedding hsep hinj e).injective
  apply Subtype.ext
  simpa only [coe_evalEmbedding_apply, one_smul] using he

end Preconnected

end deck

namespace IsQuotientCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B}

/-- The deck-group action on a fiber agrees with the fiber action of a quotient
covering by the deck group. -/
theorem mulActionFiber_eq_deck (hp : IsQuotientCoveringMap p (deck p)) (b : B) :
    hp.mulActionFiber b = deck.instMulActionFiber p b :=
  rfl

end IsQuotientCoveringMap

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B}

/-- A deck transformation of a covering map with preconnected total space is the
identity if it fixes a point. This specializes the uniqueness theorem for maps of
covers in May, Chapter 3, §7, p. 29, by comparing a deck transformation with the
identity, via `deck.eq_one_of_smul_eq`. No connectedness or local path connectedness
of the base, or surjectivity of the covering, is needed. -/
theorem eq_one_of_deck_smul_eq (hp : IsCoveringMap p) [PreconnectedSpace E]
    {g : deck p} {e : E} (he : g • e = e) : g = 1 := by
  exact deck.eq_one_of_smul_eq hp.isSeparatedMap hp.isLocalHomeomorph.isLocallyInjective he

end IsCoveringMap
