/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Continuous cohomology as an additive functor in the coefficients

For a fixed continuous group homomorphism, the induced maps on continuous
cohomology are additive in the coefficient morphism, in every degree.
For a fixed topological group and degree, Mathlib's continuous-cohomology
maps for the identity group homomorphism form an additive functor on topological
representations. Its action on objects and morphisms is the existing
continuous cohomology and its coefficient map, respectively.

## References

* Mathlib's continuous-representation and continuous-cohomology developments,
  by Edison Xie, Richard Hill, Andrew Yang and the Mathlib contributors,
  supply `resolutionMap`, `cochainsMap`, `map`, `map_id`, and `map_comp`.
* Mathlib's additive homology and additive functor APIs supply
  `HomologicalComplex.homologyMap_add` and `CategoryTheory.Functor.Additive`.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section CoefficientMaps

open TopRep

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max v w} k G} {Y : TopRep.{max v w} k H}

/-- The maps between standard resolutions are additive in the coefficient morphism. -/
@[simp] theorem resolutionMap_add (φ : H →ₜ* G) (f g : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ (f + g) i = resolutionMap φ f i + resolutionMap φ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- The induced homogeneous cochain map is additive in the coefficient morphism. -/
@[simp] theorem cochainsMap_add (φ : H →ₜ* G) (f g : res φ X ⟶ Y) :
    cochainsMap φ (f + g) = cochainsMap φ f + cochainsMap φ g := by
  apply HomologicalComplex.hom_ext _ _
  intro i
  simp only [HomologicalComplex.add_f_apply, cochainsMap_f]
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  simpa only [invariantsResMap, TopModuleCat.hom_ofHom, TopModuleCat.hom_add,
    _root_.add_apply, Submodule.coe_add, ContIntertwiningMap.mapInvariantsOfRes_apply,
    TopRep.hom_add, ContIntertwiningMap.add_apply] using
    congrArg (fun r => r.hom v.val) (resolutionMap_add φ f g (i + 1))

/-- Continuous cohomology maps are additive in the coefficient morphism in every degree. -/
@[simp] theorem map_add (φ : H →ₜ* G) (f g : res φ X ⟶ Y) (n : ℕ) :
    map φ (f + g) n = map φ f n + map φ g n := by
  simp only [map, cochainsMap_add, HomologicalComplex.homologyMap_add]

/-- A zero coefficient morphism induces the zero map on continuous cohomology. -/
@[simp] theorem map_zero (φ : H →ₜ* G) (n : ℕ) :
    map φ (0 : res φ X ⟶ Y) n = 0 := by
  let F : (res φ X ⟶ Y) →+
      (continuousCohomology n X ⟶ continuousCohomology n Y) :=
    AddMonoidHom.mk' (fun f => map φ f n)
      (fun f g => map_add φ f g n)
  exact F.map_zero

/-- Evaluation of the cohomology map induced by a sum of coefficient morphisms. -/
theorem map_add_apply (φ : H →ₜ* G) (f g : res φ X ⟶ Y) (n : ℕ)
    (x : continuousCohomology n X) :
    (map φ (f + g) n).hom x = (map φ f n).hom x + (map φ g n).hom x := by
  simp only [map_add, TopModuleCat.hom_add, _root_.add_apply]

end CoefficientMaps

/-- Continuous cohomology in a fixed degree and for a fixed acting group,
functorial in the topological coefficient representation. -/
noncomputable def coefficientFunctor (n : ℕ) :
    TopRep.{max v w} k G ⥤ TopModuleCat.{max v w} k where
  obj X := continuousCohomology n X
  map f := map (ContinuousMonoidHom.id G) f n
  map_id X := map_id X n
  map_comp f g := by
    have h := ContinuousCohomology.map_comp
      (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id G) f g n
    convert h using 1
    all_goals rfl

@[simp] theorem coefficientFunctor_obj (n : ℕ) (X : TopRep.{max v w} k G) :
    (coefficientFunctor (k := k) (G := G) n).obj X = continuousCohomology n X := rfl

@[simp] theorem coefficientFunctor_map (n : ℕ) {X Y : TopRep.{max v w} k G}
    (f : X ⟶ Y) :
    (coefficientFunctor (k := k) (G := G) n).map f =
      map (ContinuousMonoidHom.id G) f n := rfl

instance (n : ℕ) : (coefficientFunctor (k := k) (G := G) n).Additive where
  map_add {X Y f g} := by
    dsimp only [coefficientFunctor_obj, coefficientFunctor_map]
    exact map_add (ContinuousMonoidHom.id G) f g n

end ContinuousCohomology
