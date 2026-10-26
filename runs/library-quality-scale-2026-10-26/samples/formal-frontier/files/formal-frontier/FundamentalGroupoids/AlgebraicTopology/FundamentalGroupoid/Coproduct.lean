/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Fundamental groupoids of topological coproducts

For a family `X : ι → Type u` indexed by `ι : Type v`, with independent
universes, `FundamentalGroupoidFunctor.sigmaComparison` is the canonical
functor from the categorical sigma of the original fundamental groupoids to
the fundamental groupoid of the original topological sigma. It is exactly
`CategoryTheory.Sigma.desc` of the functors induced by the continuous summand
inclusions. The category on the source is Mathlib's sigma category.

The object and arrow equations, restriction natural isomorphism, and
bijectivity on objects are proved below. The equivalence assertion
`sigmaComparison_isEquivalence` follows from full faithfulness and object
surjectivity. It is an ordinary proposition-valued theorem, not an instance;
Mathlib's `Functor.asEquivalence` supplies equivalence data when it is installed
as a local instance.
There are no connectedness, nonemptiness, local path connectedness, finiteness,
separation, compact-generation, or basepoint assumptions on the summands.
Empty indices and empty summands are allowed.

## Implementation notes and references

The categorical sigma and its descent and restriction isomorphism are due to
Bhavik Mehta in Mathlib. The original fundamental-groupoid wrapper, path-class
arrows and induced functor are due to Shing Tak Lam. The continuous sigma
inclusions use the topology constructions of Johannes Hölzl, Mario Carneiro
and Patrick Massot and the continuous-map API of Nicolò Cavalleri in Mathlib.
Object bijectivity uses only the existing equivalences of underlying types.
For full faithfulness, Mathlib's `Continuous.exists_lift_sigma` factors paths
and path homotopies through a single summand, since the interval and its square
are connected. Injectivity of the summand inclusion recovers all endpoint and
relative-boundary equations in the original path and homotopy types. This uses
the connected-source factorization API of Johannes Hölzl, Mario Carneiro and
Yury Kudryashov; it imposes no connectedness condition on any summand.

The mathematical motivation is the all-points groupoid viewpoint of J. Peter
May, *A Concise Course in Algebraic Topology*, Chapter 2, §5, together with the
disjoint-union and coproduct viewpoint of §6. This arbitrary-family comparison
is derived support for that viewpoint, not a quoted theorem of the book.
-/

@[expose] public section

open CategoryTheory

namespace FundamentalGroupoidFunctor

universe u v

variable {ι : Type v} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

/-- The canonical comparison includes each summand's points and path classes
into the topological sigma, using the stock categorical sigma descent. -/
noncomputable def sigmaComparison :
    (Σ i, FundamentalGroupoid (X i)) ⥤ FundamentalGroupoid (Σ i, X i) :=
  CategoryTheory.Sigma.desc fun i =>
    FundamentalGroupoid.map (ContinuousMap.sigmaMk i)

/-- The comparison retains the tag and the underlying point. -/
@[simp]
theorem sigmaComparison_obj (i : ι) (x : FundamentalGroupoid (X i)) :
    (sigmaComparison X).obj ⟨i, x⟩ = FundamentalGroupoid.mk ⟨i, x.as⟩ :=
  rfl

/-- On an arrow from one summand, the comparison is the functor induced by
that summand's continuous inclusion. -/
@[simp]
theorem sigmaComparison_map_mk {i : ι} {x y : FundamentalGroupoid (X i)} (f : x ⟶ y) :
    (sigmaComparison X).map (CategoryTheory.Sigma.SigmaHom.mk f) =
      (FundamentalGroupoid.map (ContinuousMap.sigmaMk i)).map f :=
  rfl

/-- Restriction to a summand is canonically naturally isomorphic to its induced
inclusion functor, using the stock sigma restriction isomorphism. -/
noncomputable def sigmaComparisonInclIso (i : ι) :
    CategoryTheory.Sigma.incl i ⋙ sigmaComparison X ≅
      FundamentalGroupoid.map (ContinuousMap.sigmaMk i) :=
  CategoryTheory.Sigma.inclDesc
    (fun i => FundamentalGroupoid.map (ContinuousMap.sigmaMk i)) i

/-- The comparison is bijective on the original object types. This is only a
carrier-level assertion and does not assert full faithfulness. -/
theorem sigmaComparison_obj_bijective : Function.Bijective (sigmaComparison X).obj :=
  ((Equiv.sigmaCongrRight fun i => FundamentalGroupoid.equiv (X i)).trans
    (FundamentalGroupoid.equiv (Σ i, X i)).symm).bijective

open unitInterval in
private theorem homotopic_of_sigmaMk {i : ι} {x y : X i} {p q : Path x y}
    (h : (p.map (ContinuousMap.sigmaMk (X := X) i).continuous).Homotopic
      (q.map (ContinuousMap.sigmaMk (X := X) i).continuous)) : p.Homotopic q := by
  rcases h with ⟨H⟩
  obtain ⟨j, g, hg, hH⟩ := H.continuous.exists_lift_sigma
  have hji : j = i := congrArg Sigma.fst
    ((congrFun hH (0, 0)).symm.trans (H.source 0))
  subst j
  refine ⟨{
    toFun := g
    continuous_toFun := hg
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }⟩
  · intro t
    exact sigma_mk_injective ((congrFun hH (0, t)).symm.trans (H.map_zero_left t))
  · intro t
    exact sigma_mk_injective ((congrFun hH (1, t)).symm.trans (H.map_one_left t))
  · intro t s hs
    exact sigma_mk_injective
      ((congrFun hH (t, s)).symm.trans (ContinuousMap.HomotopyRel.eq_fst H t hs))

private theorem sigmaComparison_map_injective
    (a b : Σ i, FundamentalGroupoid (X i)) :
    Function.Injective ((sigmaComparison X).map (X := a) (Y := b)) := by
  intro f g h
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      apply congrArg CategoryTheory.Sigma.SigmaHom.mk
      induction f using Path.Homotopic.Quotient.ind with
      | mk p =>
        induction g using Path.Homotopic.Quotient.ind with
        | mk q =>
          exact Quotient.sound (homotopic_of_sigmaMk X (Quotient.exact h))

open unitInterval in
private theorem sigmaComparison_map_surjective
    (a b : Σ i, FundamentalGroupoid (X i)) :
    Function.Surjective ((sigmaComparison X).map (X := a) (Y := b)) := by
  rcases a with ⟨i, ⟨x⟩⟩
  rcases b with ⟨j, ⟨y⟩⟩
  intro f
  induction f using Path.Homotopic.Quotient.ind with
  | mk p =>
    obtain ⟨k, g, hg, hp⟩ := p.continuous.exists_lift_sigma
    have hki : k = i := congrArg Sigma.fst
      ((congrFun hp 0).symm.trans p.source)
    subst k
    have hij : i = j := congrArg Sigma.fst
      ((congrFun hp 1).symm.trans p.target)
    subst j
    let q : Path x y := {
      toFun := g
      continuous_toFun := hg
      source' := sigma_mk_injective ((congrFun hp 0).symm.trans p.source)
      target' := sigma_mk_injective ((congrFun hp 1).symm.trans p.target)
    }
    refine ⟨CategoryTheory.Sigma.SigmaHom.mk (Path.Homotopic.Quotient.mk q), ?_⟩
    change Path.Homotopic.Quotient.mk (q.map (ContinuousMap.sigmaMk i).continuous) =
      Path.Homotopic.Quotient.mk p
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact (congrFun hp t).symm

/-- The canonical comparison is an equivalence of categories. -/
theorem sigmaComparison_isEquivalence : (sigmaComparison X).IsEquivalence := by
  exact {
    faithful := { map_injective := fun {a b} => sigmaComparison_map_injective X a b }
    full := { map_surjective := fun {a b} => sigmaComparison_map_surjective X a b }
    essSurj := Functor.essSurj_of_surj (sigmaComparison_obj_bijective X).surjective
  }

end FundamentalGroupoidFunctor
