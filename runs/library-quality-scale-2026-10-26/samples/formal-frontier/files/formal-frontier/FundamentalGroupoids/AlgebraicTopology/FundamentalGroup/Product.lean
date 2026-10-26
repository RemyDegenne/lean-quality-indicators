/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Product
public import FundamentalGroupoids.FundamentalGroup

/-!
# Fundamental groups of indexed products

For an arbitrary family of pointed spaces, `FundamentalGroup.piMulEquiv` identifies
the fundamental group of the dependent product with the product of the coordinate
fundamental groups. The index type and the coordinate spaces may lie in independent
universes. Its forward map is induced by coordinate evaluation, and its inverse
assembles the coordinate loop classes. The equivalence is natural under families
of continuous coordinate maps and under arbitrary reindexing functions, with
image basepoints in the target products.

The construction restricts `FundamentalGroupoidFunctor.piProj` and
`FundamentalGroupoidFunctor.piAssembly` to loops at the given basepoints. The arrow
equations identify these maps with the inverse and forward directions, respectively,
of `FundamentalGroupoidFunctor.piProductIso`. Multiplication retains the endomorphism
convention: the right loop is traversed first. The target has the pointwise group
operations. No finiteness, nonempty-index, or connectedness assumption is required.

## References

* Mathlib's `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`, by
  Mark Lavrentyev, provides the endomorphism construction of the fundamental group.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Product` extends
  Mathlib's product-groupoid construction by Praneeth Kolichala to independent
  index and coordinate universes.
* Mathlib's `Mathlib.Topology.Homotopy.Product` and
  `Mathlib.Algebra.Group.Pi.Lemmas` provide path-class assembly and products of
  homomorphisms.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace FundamentalGroup

open CategoryTheory FundamentalGroupoidFunctor

variable {I : Type u} {X : I → Type v} [∀ i, TopologicalSpace (X i)]

/-- Coordinate evaluation identifies the fundamental group of a dependent product
with the product of its coordinate fundamental groups. The inverse assembles the
coordinate loop classes. -/
def piMulEquiv (p : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) p ≃* ∀ i, FundamentalGroup (X i) (p i) where
  __ := (MonoidHom.pi (fun i => map (ContinuousMap.eval i) p)).toMulHom
  invFun q := fromArrow
    ((piAssembly (fun i => TopCat.of (X i))).mapEnd
      (fun i => FundamentalGroupoid.mk (p i)) (fun i => toArrow (q i)))
  left_inv g := by
    change (piAssembly (fun i => TopCat.of (X i))).map
      (fun i => (piProj (fun i => TopCat.of (X i)) i).map (toArrow g)) = toArrow g
    exact piAssembly_map_piProj (fun i => TopCat.of (X i)) (toArrow g)
  right_inv q := by
    funext i
    change (piProj (fun i => TopCat.of (X i)) i).map
      ((piAssembly (fun i => TopCat.of (X i))).map (fun j => toArrow (q j))) =
        toArrow (q i)
    exact piProj_map_piAssembly (fun i => TopCat.of (X i)) i
      (a := fun j => FundamentalGroupoid.mk (p j))
      (b := fun j => FundamentalGroupoid.mk (p j)) (fun j => toArrow (q j))

/-- The chosen coordinate of the product equivalence is induced by evaluation. -/
@[simp]
theorem piMulEquiv_apply (p : ∀ i, X i)
    (g : FundamentalGroup (∀ i, X i) p) (i : I) :
    piMulEquiv p g i = map (ContinuousMap.eval i) p g :=
  rfl

/-- The forward homomorphism of the product equivalence is the product of the
homomorphisms induced by evaluation. -/
theorem piMulEquiv_toMonoidHom (p : ∀ i, X i) :
    (piMulEquiv p).toMonoidHom =
      MonoidHom.pi (fun i => map (ContinuousMap.eval i) p) :=
  rfl

/-- The inverse product equivalence assembles the coordinate loop classes. -/
@[simp]
theorem piMulEquiv_symm_apply (p : ∀ i, X i)
    (q : ∀ i, FundamentalGroup (X i) (p i)) :
    (piMulEquiv p).symm q =
      fromPath (Path.Homotopic.pi (fun i => toPath (q i))) :=
  rfl

/-- On groupoid arrows, the forward product equivalence is the inverse arrow map
of the product-groupoid isomorphism. -/
theorem piMulEquiv_toArrow (p : ∀ i, X i)
    (g : FundamentalGroup (∀ i, X i) p) :
    (fun i => toArrow (piMulEquiv p g i)) =
      (piProductIso (fun i => TopCat.of (X i))).inv.map (toArrow g) := by
  funext i
  rw [piMulEquiv_apply, piProductIso_inv_map_apply]
  rfl

/-- On groupoid arrows, the inverse product equivalence is the forward arrow map
of the product-groupoid isomorphism. -/
theorem piMulEquiv_symm_toArrow (p : ∀ i, X i)
    (q : ∀ i, FundamentalGroup (X i) (p i)) :
    toArrow ((piMulEquiv p).symm q) =
      (piProductIso (fun i => TopCat.of (X i))).hom.map
        (fun i => toArrow (q i) :
          (fun i => FundamentalGroupoid.mk (p i)) ⟶
            (fun i => FundamentalGroupoid.mk (p i))) := by
  rw [piMulEquiv_symm_apply, piProductIso_hom_map]

/-- On a loop representative, the chosen coordinate is the class of the
coordinatewise evaluated loop. -/
theorem piMulEquiv_fromPath (p : ∀ i, X i) (γ : Path p p) (i : I) :
    piMulEquiv p (fromPath (Path.Homotopic.Quotient.mk γ)) i =
      fromPath (Path.Homotopic.Quotient.mk (γ.map (continuous_apply i))) := by
  rw [piMulEquiv_apply]
  exact (Path.Homotopic.Quotient.mk_map γ (ContinuousMap.eval i)).symm

/-- The inverse product equivalence sends a family of loop representatives to
the class of their product path. -/
theorem piMulEquiv_symm_fromPath (p : ∀ i, X i)
    (γ : ∀ i, Path (p i) (p i)) :
    (piMulEquiv p).symm (fun i => fromPath (Path.Homotopic.Quotient.mk (γ i))) =
      fromPath (Path.Homotopic.Quotient.mk (Path.pi γ)) := by
  rw [piMulEquiv_symm_apply]
  exact piAssembly_map_mk (fun i => TopCat.of (X i))
    (fun i => FundamentalGroupoid.mk (p i)) (fun i => FundamentalGroupoid.mk (p i)) γ

/-- The product equivalence commutes coordinatewise with arbitrary continuous maps,
using the image basepoints in the target spaces. -/
theorem piMulEquiv_naturality {Y : I → Type w} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (p : ∀ i, X i)
    (g : FundamentalGroup (∀ i, X i) p) (i : I) :
    piMulEquiv (fun i => f i (p i)) (map (ContinuousMap.piMap f) p g) i =
      map (f i) (p i) (piMulEquiv p g i) := by
  simp only [piMulEquiv_apply]
  exact @Eq.trans (FundamentalGroup (Y i) (f i (p i)))
    _ (map ((f i).comp (ContinuousMap.eval i)) p g) _
    (congrArg
      (fun h : FundamentalGroup (∀ j, X j) p →*
          FundamentalGroup (Y i) (f i (p i)) => h g)
      (map_comp (ContinuousMap.eval i) (ContinuousMap.piMap f) p)).symm
    (congrArg
      (fun h : FundamentalGroup (∀ j, X j) p →*
          FundamentalGroup (Y i) (f i (p i)) => h g)
      (map_comp (f i) (ContinuousMap.eval i) p))

/-- Reindexing a product along an arbitrary function reindexes the coordinates
of its fundamental-group product equivalence. -/
theorem piMulEquiv_reindex {J : Type z} (r : J → I) (p : ∀ i, X i)
    (g : FundamentalGroup (∀ i, X i) p) (j : J) :
    piMulEquiv (fun j => p (r j)) (map (ContinuousMap.precomp r) p g) j =
      piMulEquiv p g (r j) := by
  simp only [piMulEquiv_apply]
  exact (congrArg
    (fun h : FundamentalGroup (∀ i, X i) p →*
        FundamentalGroup (X (r j)) (p (r j)) => h g)
    (map_comp (ContinuousMap.eval j) (ContinuousMap.precomp r) p)).symm

end FundamentalGroup
