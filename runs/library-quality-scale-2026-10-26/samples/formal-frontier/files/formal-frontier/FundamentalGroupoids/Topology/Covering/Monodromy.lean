/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy stabilizers, path components and maps of fibers

For a covering map, the loops fixing a point of a fiber are exactly the image of the
fundamental group of the total space based at that point. Two points of a fiber lie in the
same monodromy orbit exactly when they are joined by a path in the total space.

The stabilizer and orbit statements use Mathlib's covering maps, which need not be
surjective. Unlike the connected, locally path-connected setting of May's covering-space
theory, they need no global connectedness, local path-connectedness, or separation assumptions.

Path connectedness of the total space makes the canonical monodromy action pretransitive at
any basepoint. Over a path-connected base, the converse holds for nonempty total spaces,
without local path connectedness: every path component meets the chosen fiber. Thus path
connectedness of the total space is equivalent to its nonemptiness and monodromy
pretransitivity. Nonemptiness is necessary because an empty fiber has a pretransitive action.

The monodromy and path-lifting constructions are those of Mathlib's prior formalization by
Junyan Xu in `Mathlib.Topology.Homotopy.Lifting`. In particular, the point stabilizer below
is not the kernel of the permutation representation for a general covering map. For quotient
coverings, Mathlib's `IsQuotientCoveringMap.monodromy_eq_id_iff` identifies these conditions,
and `IsQuotientCoveringMap.ker_monodromyPerm` already computes that kernel.

Continuous maps over a common base intertwine monodromy. The proof generalizes the
lifted-path-class argument of Mathlib's `IsQuotientCoveringMap.monodromy_toPermFiber`;
`IsQuotientCoveringMap.monodromy_naturality_toPermFiber` recovers its quotient-action
formula. Restriction to a point fiber is the equivariant map `IsCoveringMap.fiberMap`
for the two covering maps' canonical fundamental-group actions, without connectivity
hypotheses. Restriction preserves identities and composition.

Over a path-connected base, continuous maps out of a covering space are determined by their
values on one whole fiber when the target projection is separated and locally injective.
This uniqueness requires no local path connectedness.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §§2–4,
  especially the monodromy discussion on p. 25.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, p. 29,
  for restriction of maps of covering spaces to a fiber and uniqueness.
* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering-space monodromy and lifting.
* Kenny Lau and Antoine Chambert-Loir, `Mathlib.GroupTheory.GroupAction.Hom`, for
  equivariant maps.
* Chris Hughes and Yury Kudryashov, `Mathlib.Algebra.Group.Action.Pretransitive`, for
  pretransitive actions.
-/

@[expose] public section

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

namespace IsCoveringMap

variable (cov : IsCoveringMap p) {x : X}

set_option backward.isDefEq.respectTransparency.types false in
/-- A loop fixes a point of the fiber under monodromy if and only if it belongs to the image
of the fundamental group of the total space based at that point. This is the point-stabilizer
formulation of the covering-space correspondence in May, Chapter 3, §§2–4, without global
connectedness or local path-connectedness assumptions. No regularity of the covering is assumed. -/
theorem monodromy_eq_self_iff_mem_range (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    cov.monodromy γ e = e ↔
      γ ∈ (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2).range := by
  constructor
  · intro h
    refine ⟨(cov.liftPathQuotient γ e).cast rfl (congrArg Subtype.val h.symm), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
      cov.map_liftPathQuotient]
    simp
  · rintro ⟨Γ, rfl⟩
    apply cov.monodromy_eq_of_map_eq Γ
    rw [FundamentalGroup.mapOfEq_apply]
    simp

/-- Two points of a fiber lie in the same monodromy orbit if and only if they are joined by a
path in the total space. This is the orbit formulation of the covering-space correspondence in
May, Chapter 3, §§2–4. If the total space is path-connected, this equivalence yields transitivity;
the equivalence itself needs no such assumption. -/
theorem exists_monodromy_eq_iff_joined (e e' : p ⁻¹' {x}) :
    (∃ γ : FundamentalGroup X x, cov.monodromy γ e = e') ↔ Joined e.1 e'.1 := by
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨Γ⟩ := cov.liftPathQuotient γ e
    exact ⟨Γ⟩
  · rintro ⟨Γ⟩
    let γ := (Path.Homotopic.Quotient.mk Γ).map ⟨p, cov.continuous⟩
    refine ⟨γ.cast e.2.symm e'.2.symm, cov.monodromy_eq_of_map_eq (.mk Γ) ?_⟩
    exact ((γ.cast_cast e.2.symm e'.2.symm e.2 e'.2).trans γ.cast_rfl_rfl).symm

/-- A path-connected total space makes canonical monodromy pretransitive on every fiber.
No connectedness assumption on the base is needed, and the fiber may be empty. This is the
pretransitivity consequence of the orbit correspondence in May, Chapter 3, §§2–4. -/
theorem monodromy_isPretransitive (b : X) [PathConnectedSpace E] :
    @MulAction.IsPretransitive (FundamentalGroup X b) (p ⁻¹' {b})
      (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul := by
  refine @MulAction.IsPretransitive.mk (FundamentalGroup X b) (p ⁻¹' {b})
    (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul ?_
  intro e e'
  exact (cov.exists_monodromy_eq_iff_joined e e').mpr (PathConnectedSpace.joined _ _)

/-- Over a path-connected base, pretransitive canonical monodromy makes a nonempty total
space path-connected. Each path component meets the chosen fiber, so no local path
connectedness assumption is needed. Nonemptiness excludes the empty covering, whose
monodromy action is vacuously pretransitive. -/
theorem pathConnectedSpace_of_monodromy_isPretransitive (b : X)
    [PathConnectedSpace X] [Nonempty E]
    (h : @MulAction.IsPretransitive (FundamentalGroup X b) (p ⁻¹' {b})
      (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul) : PathConnectedSpace E := by
  refine ⟨inferInstance, ?_⟩
  intro e e'
  obtain ⟨a, ha⟩ := cov.comp_subtypeVal_pathComponent_surjective e b
  obtain ⟨a', ha'⟩ := cov.comp_subtypeVal_pathComponent_surjective e' b
  have hjoined : Joined a.val a'.val :=
    (cov.exists_monodromy_eq_iff_joined ⟨a.val, ha⟩ ⟨a'.val, ha'⟩).mp
      (h.exists_smul_eq ⟨a.val, ha⟩ ⟨a'.val, ha'⟩)
  exact (mem_pathComponent_iff.mp a.property).trans
    (hjoined.trans (mem_pathComponent_iff.mp a'.property).symm)

/-- Over a path-connected base, the total space is path-connected exactly when it is
nonempty and its canonical monodromy action on the chosen fiber is pretransitive. The
nonemptiness condition is essential: monodromy on the empty covering is pretransitive. -/
theorem pathConnectedSpace_iff_nonempty_and_monodromy_isPretransitive (b : X)
    [PathConnectedSpace X] :
    PathConnectedSpace E ↔ Nonempty E ∧
      @MulAction.IsPretransitive (FundamentalGroup X b) (p ⁻¹' {b})
        (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul := by
  constructor
  · intro h
    have := h
    exact ⟨h.nonempty, cov.monodromy_isPretransitive b⟩
  · rintro ⟨hne, h⟩
    have := hne
    exact cov.pathConnectedSpace_of_monodromy_isPretransitive b h

end IsCoveringMap

section Maps

universe u v w z

variable {E : Type u} {E' : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : E → B} {q : E' → B}

namespace IsCoveringMap

/-- Monodromy is natural for continuous maps between covering spaces over the same base.
This uses the lifted homotopy class of a path, without connectivity hypotheses. -/
theorem monodromy_naturality (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (f : C(E, E')) (hf : q ∘ f = p) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    covq.monodromy γ ⟨f e, (congr_fun hf e).trans e.2⟩ =
      ⟨f (covp.monodromy γ e),
        (congr_fun hf (covp.monodromy γ e)).trans (covp.monodromy γ e).2⟩ := by
  let Γ := covp.liftPathQuotient γ e
  let p' : C(E, B) := ⟨p, covp.continuous⟩
  let q' : C(E', B) := ⟨q, covq.continuous⟩
  have hcomp : q'.comp f = p' := ContinuousMap.ext fun z ↦ congr_fun hf z
  apply covq.monodromy_eq_of_map_eq (Γ.map f)
  rw [← Path.Homotopic.Quotient.map_comp]
  convert covp.map_liftPathQuotient γ e using 2
  · exact congr_fun hf e
  · exact congr_fun hf (covp.monodromy γ e)
  · grind

/-- Restriction of a continuous map over the base to an equivariant map of point fibers.
Both actions are the specified covering maps' canonical fundamental-group actions. No
connectedness, local path connectedness or surjectivity is required. -/
def fiberMap (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p}) :
    @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul :=
  @MulActionHom.mk (FundamentalGroup B b) (FundamentalGroup B b)
    (@id (FundamentalGroup B b))
    (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
    (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
    (fun e ↦ ⟨f.val e.val, (congr_fun f.property e.val).trans e.property⟩)
    (fun γ e ↦ (covp.monodromy_naturality covq f.val f.property γ e).symm)

/-- Restriction evaluates the original continuous map on the fiber. -/
theorem fiberMap_apply (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p}) (e : p ⁻¹' {b}) :
    covp.fiberMap covq b f e =
      ⟨f.val e.val, (congr_fun f.property e.val).trans e.property⟩ := rfl

/-- The total-space coordinate of restriction is evaluation of the original map. -/
@[simp] theorem fiberMap_apply_coe (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p}) (e : p ⁻¹' {b}) :
    (covp.fiberMap covq b f e).val = f.val e.val := rfl

/-- An equivariant map is the restriction of an over-map exactly when their underlying
values agree on the whole fiber. -/
theorem fiberMap_eq_iff (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p})
    {h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul} :
    covp.fiberMap covq b f = h ↔ ∀ e : p ⁻¹' {b}, f.val e.val = (h e).val := by
  constructor
  · intro hf e
    exact congrArg Subtype.val (DFunLike.congr_fun hf e)
  · intro hf
    exact DFunLike.ext _ _ fun e ↦ Subtype.ext (hf e)

/-- Restriction of the identity over-map is the identity equivariant map. -/
@[simp] theorem fiberMap_id (covp : IsCoveringMap p) (b : B) :
    covp.fiberMap covp b ⟨ContinuousMap.id E, rfl⟩ =
      @MulActionHom.id (FundamentalGroup B b) (p ⁻¹' {b})
        (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul := by
  exact DFunLike.ext _ _ fun _ ↦ Subtype.ext rfl

section Composition

variable {E'' : Type z} [TopologicalSpace E''] {r : E'' → B}

/-- Restriction preserves composition of continuous maps over the base. The three total
spaces and the base have independent universes. -/
@[simp] theorem fiberMap_comp (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (covr : IsCoveringMap r) (b : B)
    (g : {g : C(E', E'') // r ∘ g = q}) (f : {f : C(E, E') // q ∘ f = p}) :
    covp.fiberMap covr b
      ⟨g.val.comp f.val, funext fun e ↦
        (congr_fun g.property (f.val e)).trans (congr_fun f.property e)⟩ =
      @MulActionHom.comp (FundamentalGroup B b) (FundamentalGroup B b)
        (FundamentalGroup B b) (@id (FundamentalGroup B b)) (@id (FundamentalGroup B b))
        (@id (FundamentalGroup B b))
        (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (r ⁻¹' {b}) (covr.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (covq.fiberMap covr b g) (covp.fiberMap covq b f) inferInstance := by
  exact DFunLike.ext _ _ fun _ ↦ Subtype.ext rfl

end Composition

/-- Continuous maps over a path-connected base from a covering space to a separated,
locally injective map agree everywhere if they agree on one whole fiber. Every path component
of the source meets that fiber, and uniqueness of lifts applies on each component. No local
path connectedness, total-space connectedness, nonemptiness, or surjectivity is required. -/
theorem eq_of_comp_eq_of_eqOn_fiber (covp : IsCoveringMap p) (hsep : IsSeparatedMap q)
    (hinj : IsLocallyInjective q) [PathConnectedSpace B] (f g : C(E, E'))
    (hf : q ∘ f = p) (hg : q ∘ g = p) (b : B)
    (h : ∀ e : p ⁻¹' {b}, f e = g e) : f = g := by
  ext e
  obtain ⟨a, ha⟩ := covp.comp_subtypeVal_pathComponent_surjective e b
  exact hsep.eqOn_of_comp_eqOn hinj isPathConnected_pathComponent.isConnected.isPreconnected
    f.continuous.continuousOn g.continuous.continuousOn
    (fun z _ ↦ congr_fun (hf.trans hg.symm) z) a.property (h ⟨a, ha⟩)
    (mem_pathComponent_self e)

/-- Restriction to a whole fiber is injective over a path-connected base. The total spaces
need not be connected, locally path connected or nonempty. -/
theorem fiberMap_injective (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    [PathConnectedSpace B] (b : B) : Function.Injective (covp.fiberMap covq b) := by
  intro f g h
  apply Subtype.ext
  exact covp.eq_of_comp_eq_of_eqOn_fiber covq.isSeparatedMap
    covq.isLocalHomeomorph.isLocallyInjective f.val g.val f.property g.property b
    ((covp.fiberMap_eq_iff covq b f).mp h)

end IsCoveringMap

end Maps

namespace IsQuotientCoveringMap

variable {G : Type*} [Group G] [MulAction G E] (hp : IsQuotientCoveringMap p G) {x : X}

/-- Naturality for the continuous action defining a quotient covering recovers the
`IsQuotientCoveringMap.monodromy_toPermFiber` formula. Thus the naturality statement for
arbitrary covering maps specializes to the quotient-covering commutation law. -/
theorem monodromy_naturality_toPermFiber {y : X} (γ : Path.Homotopic.Quotient x y)
    (g : G) (e : p ⁻¹' {x}) :
    hp.isCoveringMap.monodromy γ (hp.toPermFiber x g e) =
      hp.toPermFiber y g (hp.isCoveringMap.monodromy γ e) := by
  exact hp.isCoveringMap.monodromy_naturality hp.isCoveringMap
    ⟨fun z ↦ g • z, hp.toContinuousConstSMul.continuous_const_smul g⟩
    (funext fun _ ↦ hp.map_smul g) γ e

/-- For a quotient covering, fixing one point of a fiber under monodromy is equivalent to
acting trivially on the whole fiber. Thus the kernel of the monodromy representation is the
preimage of any point stabilizer. Combined with
`IsCoveringMap.monodromy_eq_self_iff_mem_range`, this recovers
`IsQuotientCoveringMap.ker_monodromyPerm`. -/
theorem ker_monodromyPerm_eq_comap_stabilizer (e : p ⁻¹' {x}) :
    (hp.isCoveringMap.monodromyPerm x).ker =
      (MulAction.stabilizer (Equiv.Perm (p ⁻¹' {x})) e).comap
        (hp.isCoveringMap.monodromyPerm x) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  simpa only [DFunLike.ext'_iff, IsCoveringMap.coe_monodromyPerm, Equiv.Perm.coe_one,
    Equiv.Perm.smul_def] using hp.monodromy_eq_id_iff e (γ := γ)

end IsQuotientCoveringMap
