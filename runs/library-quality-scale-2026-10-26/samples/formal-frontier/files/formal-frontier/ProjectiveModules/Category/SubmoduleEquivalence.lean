/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Submodule lattices under module-category equivalences

An ordinary equivalence between categories of left modules induces an order
isomorphism between their lattices of submodules. Its forward map is the range
of the image of a submodule inclusion. Its inverse map uses the inverse functor
and the inverse of the unit isomorphism to return to the original module.

The scalar and carrier universes are independent. The rings need not be
commutative, and no additive or linear structure on the equivalence is assumed.
The identity and composition laws describe the coherence of this transport.

## References

The construction uses Mathlib's module-subobject correspondence by Markus Himmel,
subobject equivalences by Bhavik Mehta and Kim Morrison, and the equivalence/order
isomorphism API by Stephen Morgan, Kim Morrison, Johannes Hölzl and Reid Barton.
It follows the submodule-lattice construction in
`ModuleCat.finite_iff_of_equivalence` by Formal Frontier Agents.
-/

@[expose] public section

universe uR uS uT vR vS vT

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The order isomorphism on all submodules induced by an ordinary equivalence of
categories of left modules, with independent scalar and carrier universes. -/
noncomputable def submoduleOrderIsoOfEquivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    Submodule R X ≃o Submodule S (e.functor.obj X) :=
  (subobjectModule X).symm.trans
    ((Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso.trans
      (subobjectModule (e.functor.obj X)))

private theorem subobjectModule_mk_range {X Y : ModuleCat.{vR} R}
    (i : Y ⟶ X) [Mono i] :
    subobjectModule X (Subobject.mk i) = LinearMap.range i.hom := by
  change LinearMap.range (Subobject.mk i).arrow.hom = LinearMap.range i.hom
  rw [← Subobject.underlyingIso_hom_comp_eq_mk i, hom_comp]
  exact LinearEquiv.range_comp (Subobject.underlyingIso i).toLinearEquiv i.hom

private theorem submoduleOrderIsoOfEquivalence_range
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) {X Y : ModuleCat.{vR} R}
    (i : Y ⟶ X) [Mono i] :
    submoduleOrderIsoOfEquivalence e X (LinearMap.range i.hom) =
      LinearMap.range (e.functor.map i).hom := by
  change subobjectModule (e.functor.obj X)
    ((Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso
      ((subobjectModule X).symm (LinearMap.range i.hom))) = _
  rw [← subobjectModule_mk_range i, OrderIso.symm_apply_apply]
  exact subobjectModule_mk_range (e.functor.map i)

/-- Forward transport of a submodule is the range of its inclusion after applying
 the equivalence's forward functor. -/
@[simp]
theorem submoduleOrderIsoOfEquivalence_apply
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R)
    (N : Submodule R X) :
    submoduleOrderIsoOfEquivalence e X N =
      LinearMap.range ((e.functor.map (ofHom N.subtype)).hom) := by
  simpa only [hom_ofHom, Submodule.range_subtype] using
    submoduleOrderIsoOfEquivalence_range e (ofHom N.subtype)

/-- Inverse transport applies the inverse functor to the inclusion and then uses
 the inverse unit isomorphism to land in the original module. -/
@[simp]
theorem submoduleOrderIsoOfEquivalence_symm_apply
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R)
    (P : Submodule S (e.functor.obj X)) :
    (submoduleOrderIsoOfEquivalence e X).symm P =
      LinearMap.range
        ((e.inverse.map (ofHom P.subtype) ≫ (e.unitIso.app X).inv).hom) := by
  change subobjectModule X
    (Subobject.mk (e.inverse.map (ofHom P.subtype) ≫ (e.unitIso.app X).inv)) = _
  exact subobjectModule_mk_range _

/-- Transport along the identity equivalence is the identity on submodules. -/
@[simp]
theorem submoduleOrderIsoOfEquivalence_refl (X : ModuleCat.{vR} R) :
    submoduleOrderIsoOfEquivalence (CategoryTheory.Equivalence.refl (C := ModuleCat.{vR} R)) X =
      OrderIso.refl (Submodule R X) := by
  apply OrderIso.ext
  funext N
  rw [submoduleOrderIsoOfEquivalence_apply]
  exact Submodule.range_subtype N

/-- Transport along a composite equivalence is the composite of the two
submodule order isomorphisms, with an independent third ring and carrier universe. -/
theorem submoduleOrderIsoOfEquivalence_trans
    {T : Type uT} [Ring T]
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S)
    (f : ModuleCat.{vS} S ≌ ModuleCat.{vT} T) (X : ModuleCat.{vR} R) :
    submoduleOrderIsoOfEquivalence (e.trans f) X =
      (submoduleOrderIsoOfEquivalence e X).trans
        (submoduleOrderIsoOfEquivalence f (e.functor.obj X)) := by
  apply OrderIso.ext
  funext N
  change submoduleOrderIsoOfEquivalence (e.trans f) X N =
    submoduleOrderIsoOfEquivalence f (e.functor.obj X)
      (submoduleOrderIsoOfEquivalence e X N)
  rw [submoduleOrderIsoOfEquivalence_apply (e.trans f),
    submoduleOrderIsoOfEquivalence_apply e]
  exact (submoduleOrderIsoOfEquivalence_range f
    (e.functor.map (ofHom N.subtype))).symm

end ModuleCat
