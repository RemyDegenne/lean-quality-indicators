/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Monodromy
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Monodromy orbit classes and path components

Monodromy orbit classes of a point fiber of a covering map are equivalent to the
fiber of the induced map on path components. The induced map is Mathlib's
`Quotient.map` on the path setoids, and the equivalence sends the class of a fiber point
`e` to its component `ZerothHomotopy.mk e.val`, with the fiber-membership proof.
No path-connectedness of the base or total space is needed. For every point `e`, the
covering map also satisfies `p '' pathComponent e = pathComponent (p e)`.

Over a path-connected base, the orbit classes are equivalent to all path components of
the total space. The total space need not be nonempty or locally path-connected, and
the covering map need not be surjective.

The representative formula determines the forward map uniquely by the quotient universal
property, `Setoid.lift_unique` or `Setoid.liftEquiv`. The inverse representative formula
follows from the inverse laws for equivalences.

The embedding uses the orbit–path correspondence in
`IsCoveringMap.exists_monodromy_eq_iff_joined`, followed by the quotient-kernel-to-range
equivalence. Membership in the component-map fiber follows from a point-fiber
representative. The component-map-fiber equivalence upgrades this embedding using
its surjectivity and `Function.Embedding.equivOfSurjective`. The equivalence over a
path-connected base additionally uses
`IsCoveringMap.comp_subtypeVal_pathComponent_surjective`. The action, orbit quotient and
path-component carrier are Mathlib's constructions.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §§2–4, for monodromy
  background, especially the discussion on p. 25.
* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering-space monodromy and the
  component-meets-fiber theorem.
* Mathlib's `MulAction.orbitRel.Quotient`, `ZerothHomotopy`, and quotient universal property.
-/

@[expose] public section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsCoveringMap

variable (cov : IsCoveringMap p)

-- The kernel of the component-class map is exactly the monodromy orbit relation.
-- No path-connectedness assumption on the base is needed.
private theorem monodromyOrbit_ker (b : B) :
    Setoid.ker (fun e : p ⁻¹' {b} ↦ ZerothHomotopy.mk e.val) =
      @MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b) := by
  let := cov.fundamentalGroupMulAction b
  refine Setoid.ext fun e e' ↦ ?_
  rw [Setoid.ker_def, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fun h ↦ (cov.exists_monodromy_eq_iff_joined e' e).mpr
      (Joined.symm (Quotient.exact h)),
    fun h ↦ Quotient.sound
      (Joined.symm ((cov.exists_monodromy_eq_iff_joined e' e).mp h))⟩

-- Every path component is represented by a point of the chosen fiber.
include cov in
private theorem monodromyOrbit_surjective (b : B) [PathConnectedSpace B] :
    Function.Surjective (fun e : p ⁻¹' {b} ↦ ZerothHomotopy.mk e.val) := by
  intro c
  obtain ⟨e, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨a, ha⟩ := cov.comp_subtypeVal_pathComponent_surjective e b
  refine ⟨⟨a.val, ha⟩, ?_⟩
  exact Quotient.sound (mem_pathComponent_iff.mp a.property).symm

/-- Monodromy orbit classes in a point fiber of a covering map correspond to path components
of the total space over a path-connected base. This uses the covering map's canonical
fundamental-group action and allows an empty total space. -/
noncomputable def monodromyOrbitEquivZerothHomotopy (b : B) [hB : PathConnectedSpace B] :
    @MulAction.orbitRel.Quotient (FundamentalGroup B b) (p ⁻¹' {b}) _
      (cov.fundamentalGroupMulAction b) ≃ ZerothHomotopy E := by
  letI := cov.fundamentalGroupMulAction b
  -- `let` retains the Prop-valued term `by` boundary for private lemmas.
  -- Tactic `have` would strip that boundary.
  let hdesc : MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) ≤
      Setoid.ker (fun e : p ⁻¹' {b} ↦ ZerothHomotopy.mk e.val) := by
    exact le_of_eq (monodromyOrbit_ker cov b).symm
  exact Equiv.ofBijective (Quotient.lift (fun e ↦ ZerothHomotopy.mk e.val) hdesc) (by
    exact ⟨(Setoid.lift_injective_iff_ker_eq_of_le hdesc).mpr (monodromyOrbit_ker cov b),
      Quotient.lift_surjective _ hdesc (monodromyOrbit_surjective cov b)⟩)

/-- The orbit class of a fiber point maps to its path component in the total space. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopy_apply (b : B) [PathConnectedSpace B]
    (e : p ⁻¹' {b}) :
    cov.monodromyOrbitEquivZerothHomotopy b
      (Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e) = ZerothHomotopy.mk e.val := rfl

/-- The component of a fiber point maps back to its monodromy orbit class. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopy_symm_apply (b : B) [PathConnectedSpace B]
    (e : p ⁻¹' {b}) :
    (cov.monodromyOrbitEquivZerothHomotopy b).symm (ZerothHomotopy.mk e.val) =
      Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e := by
  rw [← cov.monodromyOrbitEquivZerothHomotopy_apply b e]
  exact (cov.monodromyOrbitEquivZerothHomotopy b).symm_apply_apply _

/-- Monodromy orbit classes in a point fiber embed into the fiber of the induced map on
path components. The action is the covering map's canonical fundamental-group action;
the induced map is `Quotient.map` on the path setoids. No path-connectedness assumption
on the base or total space is required. -/
noncomputable def monodromyOrbitEmbeddingZerothHomotopyFiber (b : B) :
    @MulAction.orbitRel.Quotient (FundamentalGroup B b) (p ⁻¹' {b}) _
      (cov.fundamentalGroupMulAction b) ↪
      {c : ZerothHomotopy E //
        @Quotient.map E B (pathSetoid E) (pathSetoid B) p
          (fun _ _ h ↦ h.map cov.continuous) c = ZerothHomotopy.mk b} := by
  let f : p ⁻¹' {b} → ZerothHomotopy E := fun e ↦ ZerothHomotopy.mk e.val
  let hker : ∀ e e' : p ⁻¹' {b},
      @MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b) e e' ↔ Setoid.ker f e e' := by
    exact Setoid.ext_iff.1 (monodromyOrbit_ker cov b).symm
  let hmem : ∀ c : ZerothHomotopy E, c ∈ Set.range f →
      @Quotient.map E B (pathSetoid E) (pathSetoid B) p
        (fun _ _ h ↦ h.map cov.continuous) c = ZerothHomotopy.mk b := by
    rintro c ⟨e, rfl⟩
    exact congrArg ZerothHomotopy.mk e.property
  exact ((Quotient.congrRight hker).trans
    (Setoid.quotientKerEquivRange f)).toEmbedding.trans (Subtype.impEmbedding _ _ hmem)

/-- The underlying component of the image of a fiber-point orbit is the component of
that point. -/
@[simp] theorem monodromyOrbitEmbeddingZerothHomotopyFiber_val_apply (b : B)
    (e : p ⁻¹' {b}) :
    (cov.monodromyOrbitEmbeddingZerothHomotopyFiber b
      (Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e)).val = ZerothHomotopy.mk e.val := rfl

/-- The image of a fiber-point orbit, including its membership in the component-map fiber. -/
@[simp] theorem monodromyOrbitEmbeddingZerothHomotopyFiber_apply (b : B)
    (e : p ⁻¹' {b}) :
    cov.monodromyOrbitEmbeddingZerothHomotopyFiber b
      (Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e) =
      ⟨ZerothHomotopy.mk e.val, by
        exact congrArg ZerothHomotopy.mk e.property⟩ := by
  apply Subtype.ext
  exact cov.monodromyOrbitEmbeddingZerothHomotopyFiber_val_apply b e

/-- Forgetting the fiber-membership proof leaves an injective map on orbit classes. -/
theorem monodromyOrbitEmbeddingZerothHomotopyFiber_val_injective (b : B) :
    Function.Injective (fun q ↦ (cov.monodromyOrbitEmbeddingZerothHomotopyFiber b q).val) := by
  intro q q' h
  exact (cov.monodromyOrbitEmbeddingZerothHomotopyFiber b).injective (Subtype.ext h)

/-- Over a path-connected base, forgetting fiber membership agrees with the equivalence
to all path components. This is equality of values, characterized on representatives. -/
theorem monodromyOrbitEmbeddingZerothHomotopyFiber_val_eq_monodromyOrbitEquivZerothHomotopy
    (b : B) [PathConnectedSpace B]
    (q : @MulAction.orbitRel.Quotient (FundamentalGroup B b) (p ⁻¹' {b}) _
      (cov.fundamentalGroupMulAction b)) :
    (cov.monodromyOrbitEmbeddingZerothHomotopyFiber b q).val =
      cov.monodromyOrbitEquivZerothHomotopy b q := by
  refine Quotient.inductionOn q ?_
  intro e
  rw [cov.monodromyOrbitEmbeddingZerothHomotopyFiber_val_apply,
    cov.monodromyOrbitEquivZerothHomotopy_apply]

/-- Every path component whose image is the component of the basepoint is represented
by a monodromy orbit in the point fiber. -/
theorem monodromyOrbitEmbeddingZerothHomotopyFiber_surjective (b : B) :
    Function.Surjective (cov.monodromyOrbitEmbeddingZerothHomotopyFiber b) := by
  rintro ⟨c, hc⟩
  obtain ⟨e, rfl⟩ := ZerothHomotopy.mk_surjective c
  have hbase : ZerothHomotopy.mk (p e) = ZerothHomotopy.mk b := hc
  obtain ⟨γ⟩ : Joined (p e) b := Quotient.exact hbase
  let Γ := cov.liftPath γ e γ.source
  have ha : p (Γ 1) = b :=
    (congr_fun (cov.liftPath_lifts γ e γ.source) 1).trans γ.target
  have hΓ : Joined e (Γ 1) :=
    ⟨⟨Γ, cov.liftPath_zero γ e γ.source, rfl⟩⟩
  let a : p ⁻¹' {b} := ⟨Γ 1, ha⟩
  refine ⟨Quotient.mk
    (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
      (cov.fundamentalGroupMulAction b)) a, ?_⟩
  apply Subtype.ext
  rw [cov.monodromyOrbitEmbeddingZerothHomotopyFiber_val_apply]
  exact Quotient.sound hΓ.symm

/-- Monodromy orbit classes in a point fiber of a covering map correspond to the fiber
of the induced map on path components over the basepoint component. The action is the
covering map's canonical fundamental-group action, and the induced map is `Quotient.map`
on the path setoids. No path-connectedness, local path-connectedness or surjectivity
assumption is required. -/
noncomputable def monodromyOrbitEquivZerothHomotopyFiber (b : B) :
    @MulAction.orbitRel.Quotient (FundamentalGroup B b) (p ⁻¹' {b}) _
      (cov.fundamentalGroupMulAction b) ≃
      {c : ZerothHomotopy E //
        @Quotient.map E B (pathSetoid E) (pathSetoid B) p
          (fun _ _ h ↦ h.map cov.continuous) c = ZerothHomotopy.mk b} :=
  (cov.monodromyOrbitEmbeddingZerothHomotopyFiber b).equivOfSurjective
    (cov.monodromyOrbitEmbeddingZerothHomotopyFiber_surjective b)

/-- The equivalence retains the monodromy orbit embedding as its forward embedding. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopyFiber_toEmbedding (b : B) :
    (cov.monodromyOrbitEquivZerothHomotopyFiber b).toEmbedding =
      cov.monodromyOrbitEmbeddingZerothHomotopyFiber b := rfl

/-- The underlying component of a fiber-point orbit is the component of that point. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopyFiber_val_apply (b : B)
    (e : p ⁻¹' {b}) :
    (cov.monodromyOrbitEquivZerothHomotopyFiber b
      (Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e)).val = ZerothHomotopy.mk e.val :=
  cov.monodromyOrbitEmbeddingZerothHomotopyFiber_val_apply b e

/-- The orbit class of a fiber point maps to its component in the component-map fiber. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopyFiber_apply (b : B)
    (e : p ⁻¹' {b}) :
    cov.monodromyOrbitEquivZerothHomotopyFiber b
      (Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e) =
      ⟨ZerothHomotopy.mk e.val, by
        exact congrArg ZerothHomotopy.mk e.property⟩ :=
  cov.monodromyOrbitEmbeddingZerothHomotopyFiber_apply b e

/-- The component of a fiber point maps back to its monodromy orbit class. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopyFiber_symm_apply (b : B)
    (e : p ⁻¹' {b}) :
    (cov.monodromyOrbitEquivZerothHomotopyFiber b).symm
      ⟨ZerothHomotopy.mk e.val, by
        exact congrArg ZerothHomotopy.mk e.property⟩ =
      Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e := by
  rw [← cov.monodromyOrbitEquivZerothHomotopyFiber_apply b e]
  exact (cov.monodromyOrbitEquivZerothHomotopyFiber b).symm_apply_apply _

include cov in
/-- A covering map sends the path component of a point onto the path component of its image. -/
theorem image_pathComponent (e : E) :
    p '' pathComponent e = pathComponent (p e) := by
  refine (cov.continuous.image_pathComponent_subset e).antisymm ?_
  intro y hy
  obtain ⟨γ⟩ := mem_pathComponent_iff.mp hy
  let Γ := cov.liftPath γ e γ.source
  refine ⟨Γ 1, ?_, ?_⟩
  · apply mem_pathComponent_iff.mpr
    exact ⟨⟨Γ, cov.liftPath_zero γ e γ.source, rfl⟩⟩
  · exact (congr_fun (cov.liftPath_lifts γ e γ.source) 1).trans γ.target

-- Under path-connectedness of the base, `image_pathComponent` recovers the existing
-- `IsCoveringMap.comp_subtypeVal_pathComponent_surjective` from Mathlib's lifting module.
-- Keep this recovery contract private rather than add a second public facade.
include cov in
private theorem pathComponent_surjective_of_pathConnectedSpace (e : E) [PathConnectedSpace B] :
    Function.Surjective (fun x : pathComponent e ↦ p x) := by
  intro y
  have hy : y ∈ p '' pathComponent e := by
    rw [cov.image_pathComponent e]
    exact mem_pathComponent_iff.mpr (PathConnectedSpace.joined (p e) y)
  obtain ⟨x, hx, hpx⟩ := hy
  exact ⟨⟨x, hx⟩, hpx⟩

end IsCoveringMap
