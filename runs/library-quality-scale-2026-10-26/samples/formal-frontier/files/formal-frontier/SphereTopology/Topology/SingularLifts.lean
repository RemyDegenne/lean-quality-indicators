/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifts of singular simplices through covering maps

Evaluation at any point identifies lifts through a covering map with the
point fiber. Precomposition induces a bijection on lift fibers when the
original domain is simply connected and locally path connected and the new
domain is preconnected and has a specified point.

For singular simplices, the lift fibers are the subtypes of the components of
`TopCat.toSSet.map`. Restriction is the action of the singular simplicial set
on every simplex operator, including faces and degeneracies. No choice of a
vertex, and no vertex-preservation condition on an operator, is involved.
Consequently, the induced singular simplicial map is equifibered: every
naturality square is a pullback.

## Implementation notes

The topological equivalences require no surjectivity, finiteness, or
connectedness or local connectedness of the base or total space. The generic
continuous-map statements allow independent universes for all spaces. The
singular statements use the common ambient universe of `TopCat.toSSet`.

## References

The lifting input is Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`; uniqueness on a preconnected
domain is `IsCoveringMap.eq_of_comp_eq`. The singular-simplex identification
and its operator naturality are Mathlib's `TopCat.toSSetObjEquiv` and
`TopCat.toSSetObjEquiv_naturality_apply`.
-/

@[expose] public section

open CategoryTheory Convexity

namespace IsCoveringMap

section ContinuousMap

universe u v w z

variable {A : Type u} {B : Type v} {E : Type w} {X : Type z}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace X]
  {p : C(E, X)}

/-- Evaluation at a specified point identifies continuous lifts from a simply
connected, locally path connected domain with the corresponding point fiber.
The inverse is the unique lift of
`IsCoveringMap.existsUnique_continuousMap_lifts`. -/
noncomputable def continuousMapLiftEquiv (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] (f : C(A, X)) (a : A) :
    {g : C(A, E) // p.comp g = f} ≃ {e : E // p e = f a} := by
  refine Equiv.ofBijective
    (fun g => ⟨g.val a, congrArg (fun h : C(A, X) => h a) g.property⟩) ?_
  constructor
  · intro g h he
    apply Subtype.ext
    apply ContinuousMap.coe_injective
    exact hp.eq_of_comp_eq g.val.continuous h.val.continuous
      (congrArg (fun q : C(A, X) => (q : A → X))
        (g.property.trans h.property.symm)) a (congrArg Subtype.val he)
  · intro e
    obtain ⟨g, ⟨ha, hg⟩, _⟩ := hp.existsUnique_continuousMap_lifts f a e.val e.property
    exact ⟨⟨g, ContinuousMap.coe_injective hg⟩, Subtype.ext ha⟩

/-- The lift-to-fiber equivalence evaluates the underlying continuous map. -/
@[simp]
theorem continuousMapLiftEquiv_apply (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] (f : C(A, X)) (a : A)
    (g : {g : C(A, E) // p.comp g = f}) :
    (hp.continuousMapLiftEquiv f a g).val = g.val a :=
  rfl

/-- The inverse equivalence takes the prescribed value at the specified point. -/
@[simp]
theorem continuousMapLiftEquiv_symm_apply_apply (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] (f : C(A, X)) (a : A)
    (e : {e : E // p e = f a}) :
    ((hp.continuousMapLiftEquiv f a).symm e).val a = e.val := by
  have h := congrArg Subtype.val ((hp.continuousMapLiftEquiv f a).apply_symm_apply e)
  simpa only [continuousMapLiftEquiv_apply] using h

/-- The inverse equivalence is a lift of the given continuous map. -/
@[simp]
theorem continuousMapLiftEquiv_symm_apply_comp (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] (f : C(A, X)) (a : A)
    (e : {e : E // p e = f a}) :
    p.comp ((hp.continuousMapLiftEquiv f a).symm e).val = f :=
  ((hp.continuousMapLiftEquiv f a).symm e).property

/-- Precomposition gives a bijection of continuous-map lift fibers. Only the
original domain needs to be simply connected and locally path connected;
the new domain needs preconnectedness and a specified point. -/
theorem bijective_continuousMap_lift_precomp (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] [PreconnectedSpace B]
    (f : C(A, X)) (r : C(B, A)) (b : B) :
    Function.Bijective
      (fun g : {g : C(A, E) // p.comp g = f} =>
        (⟨g.val.comp r, by rw [← ContinuousMap.comp_assoc, g.property]⟩ :
          {g : C(B, E) // p.comp g = f.comp r})) := by
  constructor
  · intro g h he
    apply (hp.continuousMapLiftEquiv f (r b)).injective
    apply Subtype.ext
    exact congrArg (fun q : {g : C(B, E) // p.comp g = f.comp r} => q.val b) he
  · intro h
    let e : {e : E // p e = f (r b)} :=
      ⟨h.val b, congrArg (fun q : C(B, X) => q b) h.property⟩
    let g := (hp.continuousMapLiftEquiv f (r b)).symm e
    refine ⟨g, Subtype.ext (ContinuousMap.coe_injective ?_)⟩
    refine hp.eq_of_comp_eq (g.val.comp r).continuous h.val.continuous ?_ b
      (hp.continuousMapLiftEquiv_symm_apply_apply f (r b) e)
    funext t
    exact (congrArg (fun q : C(A, X) => q (r t)) g.property).trans
      (congrArg (fun q : C(B, X) => q t) h.property).symm

end ContinuousMap

end IsCoveringMap

namespace TopCat

universe w

variable {X Y : TopCat.{w}} (p : Y ⟶ X)

/-- Under the continuous-map description of singular simplices, the singular
map induced by a continuous map is postcomposition. -/
theorem toSSetObjEquiv_map (k : SimplexCategoryᵒᵖ)
    (u : (toSSet.obj Y).obj k) :
    X.toSSetObjEquiv k ((toSSet.map p).app k u) =
      p.hom.comp (Y.toSSetObjEquiv k u) :=
  rfl

/-- Restrict a lift of a singular simplex along an arbitrary simplex operator. -/
noncomputable def singularLiftRestrict {k l : SimplexCategoryᵒᵖ} (α : k ⟶ l)
    (s : (toSSet.obj X).obj k) :
    {u : (toSSet.obj Y).obj k // (toSSet.map p).app k u = s} →
      {u : (toSSet.obj Y).obj l //
        (toSSet.map p).app l u = (toSSet.obj X).map α s} :=
  fun u => ⟨(toSSet.obj Y).map α u.val, by
    change (toSSet.obj X).map α ((toSSet.map p).app k u.val) = _
    exact congrArg ((toSSet.obj X).map α) u.property⟩

/-- Restriction acts by the underlying singular-set operator. -/
@[simp]
theorem singularLiftRestrict_val {k l : SimplexCategoryᵒᵖ} (α : k ⟶ l)
    (s : (toSSet.obj X).obj k)
    (u : {u : (toSSet.obj Y).obj k // (toSSet.map p).app k u = s}) :
    (singularLiftRestrict p α s u).val = (toSSet.obj Y).map α u.val :=
  rfl

/-- Identity restriction leaves the underlying lift unchanged. -/
@[simp]
theorem singularLiftRestrict_id_val (k : SimplexCategoryᵒᵖ)
    (s : (toSSet.obj X).obj k)
    (u : {u : (toSSet.obj Y).obj k // (toSSet.map p).app k u = s}) :
    (singularLiftRestrict p (𝟙 k) s u).val = u.val := by
  simp

/-- Successive restrictions agree with restriction along the composite. -/
theorem singularLiftRestrict_comp_val {k l m : SimplexCategoryᵒᵖ}
    (α : k ⟶ l) (β : l ⟶ m) (s : (toSSet.obj X).obj k)
    (u : {u : (toSSet.obj Y).obj k // (toSSet.map p).app k u = s}) :
    (singularLiftRestrict p β ((toSSet.obj X).map α s)
      (singularLiftRestrict p α s u)).val =
        (singularLiftRestrict p (α ≫ β) s u).val := by
  simp

end TopCat

namespace IsCoveringMap

universe w

variable {X Y : TopCat.{w}} {p : Y ⟶ X}

/-- Evaluation at any point of the domain simplex identifies the lift fiber
of a component of `TopCat.toSSet.map p` with a topological point fiber. -/
noncomputable def singularLiftEquiv (hp : IsCoveringMap p)
    (k : SimplexCategoryᵒᵖ) (s : (TopCat.toSSet.obj X).obj k)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1))) :
    {u : (TopCat.toSSet.obj Y).obj k // (TopCat.toSSet.map p).app k u = s} ≃
      {y : Y // p y = X.toSSetObjEquiv k s x} := by
  let e : {u : (TopCat.toSSet.obj Y).obj k // (TopCat.toSSet.map p).app k u = s} ≃
      {g : C(StdSimplex ℝ (Fin (k.unop.len + 1)), Y) //
        p.hom.comp g = X.toSSetObjEquiv k s} :=
    (Y.toSSetObjEquiv k).subtypeEquiv (by
      intro u
      constructor
      · intro hu
        rw [← TopCat.toSSetObjEquiv_map p k u, hu]
      · intro hu
        apply (X.toSSetObjEquiv k).injective
        exact (TopCat.toSSetObjEquiv_map p k u).trans hu)
  exact e.trans ((show IsCoveringMap p.hom from hp).continuousMapLiftEquiv
    (X.toSSetObjEquiv k s) x)

/-- The singular lift equivalence evaluates the corresponding continuous map. -/
@[simp]
theorem singularLiftEquiv_apply (hp : IsCoveringMap p)
    (k : SimplexCategoryᵒᵖ) (s : (TopCat.toSSet.obj X).obj k)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1)))
    (u : {u : (TopCat.toSSet.obj Y).obj k // (TopCat.toSSet.map p).app k u = s}) :
    (hp.singularLiftEquiv k s x u).val = Y.toSSetObjEquiv k u.val x :=
  rfl

/-- The inverse singular lift equivalence takes the prescribed value. -/
@[simp]
theorem singularLiftEquiv_symm_apply_apply (hp : IsCoveringMap p)
    (k : SimplexCategoryᵒᵖ) (s : (TopCat.toSSet.obj X).obj k)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1)))
    (y : {y : Y // p y = X.toSSetObjEquiv k s x}) :
    Y.toSSetObjEquiv k ((hp.singularLiftEquiv k s x).symm y).val x = y.val := by
  have h := congrArg Subtype.val ((hp.singularLiftEquiv k s x).apply_symm_apply y)
  simpa only [singularLiftEquiv_apply] using h

/-- The inverse singular lift equivalence maps back to the specified simplex. -/
@[simp]
theorem singularLiftEquiv_symm_apply_map (hp : IsCoveringMap p)
    (k : SimplexCategoryᵒᵖ) (s : (TopCat.toSSet.obj X).obj k)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1)))
    (y : {y : Y // p y = X.toSSetObjEquiv k s x}) :
    (TopCat.toSSet.map p).app k ((hp.singularLiftEquiv k s x).symm y).val = s :=
  ((hp.singularLiftEquiv k s x).symm y).property

/-- Restriction of lifts is bijective for every simplex operator, including
faces omitting the zeroth vertex and all degeneracies. -/
theorem bijective_singularLiftRestrict (hp : IsCoveringMap p)
    {k l : SimplexCategoryᵒᵖ} (α : k ⟶ l) (s : (TopCat.toSSet.obj X).obj k) :
    Function.Bijective (TopCat.singularLiftRestrict p α s) := by
  let x : StdSimplex ℝ (Fin (l.unop.len + 1)) := .single 0
  let rx : StdSimplex ℝ (Fin (k.unop.len + 1)) := StdSimplex.map α.unop x
  constructor
  · intro u v huv
    apply (hp.singularLiftEquiv k s rx).injective
    apply Subtype.ext
    have heval :
        Y.toSSetObjEquiv l (TopCat.singularLiftRestrict p α s u).val x =
          Y.toSSetObjEquiv l (TopCat.singularLiftRestrict p α s v).val x :=
      congrArg
        (fun q : {u : (TopCat.toSSet.obj Y).obj l //
            (TopCat.toSSet.map p).app l u = (TopCat.toSSet.obj X).map α s} =>
          Y.toSSetObjEquiv l q.val x) huv
    exact (TopCat.toSSetObjEquiv_naturality_apply α.unop u.val x).symm.trans
      (heval.trans (TopCat.toSSetObjEquiv_naturality_apply α.unop v.val x))
  · intro v
    let y : {y : Y // p y = X.toSSetObjEquiv k s rx} :=
      ⟨Y.toSSetObjEquiv l v.val x, by
        calc
          p (Y.toSSetObjEquiv l v.val x) =
              X.toSSetObjEquiv l ((TopCat.toSSet.map p).app l v.val) x :=
            (congrArg (fun q : C(StdSimplex ℝ (Fin (l.unop.len + 1)), X) => q x)
              (TopCat.toSSetObjEquiv_map p l v.val)).symm
          _ = X.toSSetObjEquiv l ((TopCat.toSSet.obj X).map α s) x :=
            congrArg (fun q : (TopCat.toSSet.obj X).obj l => X.toSSetObjEquiv l q x)
              v.property
          _ = X.toSSetObjEquiv k s rx :=
            TopCat.toSSetObjEquiv_naturality_apply α.unop s x⟩
    let u := (hp.singularLiftEquiv k s rx).symm y
    refine ⟨u, ?_⟩
    apply (hp.singularLiftEquiv l ((TopCat.toSSet.obj X).map α s) x).injective
    apply Subtype.ext
    exact (TopCat.toSSetObjEquiv_naturality_apply α.unop u.val x).trans
      (hp.singularLiftEquiv_symm_apply_apply k s rx y)

/-- The singular simplicial map induced by a covering map is equifibered:
every naturality square for a simplex operator is a pullback. No finiteness,
nonemptiness, surjectivity, or connectedness assumptions are needed. -/
theorem toSSet_map_equifibered (hp : IsCoveringMap p) :
    NatTrans.Equifibered (TopCat.toSSet.map p) := by
  intro k l α
  refine (Limits.Types.isPullback_iff _ _ _ _).2
    ⟨(TopCat.toSSet.map p).naturality α, ?_, ?_⟩
  · intro u v ⟨h₁, h₂⟩
    have huv :
        (⟨u, rfl⟩ : {w : (TopCat.toSSet.obj Y).obj k //
          (TopCat.toSSet.map p).app k w = (TopCat.toSSet.map p).app k u}) =
          ⟨v, h₂.symm⟩ :=
      (hp.bijective_singularLiftRestrict α ((TopCat.toSSet.map p).app k u)).1
        (Subtype.ext h₁)
    exact congrArg Subtype.val huv
  · intro v s hvs
    obtain ⟨u, hu⟩ := (hp.bijective_singularLiftRestrict α s).2 ⟨v, hvs⟩
    exact ⟨u.val, congrArg Subtype.val hu, u.property⟩

/-- A finite point fiber gives finitely many lifts of a singular simplex.
No cardinality equality is used as a substitute for finiteness. -/
theorem finite_singularLift (hp : IsCoveringMap p)
    (k : SimplexCategoryᵒᵖ) (s : (TopCat.toSSet.obj X).obj k)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1)))
    [Finite {y : Y // p y = X.toSSetObjEquiv k s x}] :
    Finite {u : (TopCat.toSSet.obj Y).obj k // (TopCat.toSSet.map p).app k u = s} :=
  Finite.of_injective (hp.singularLiftEquiv k s x) (hp.singularLiftEquiv k s x).injective

end IsCoveringMap
