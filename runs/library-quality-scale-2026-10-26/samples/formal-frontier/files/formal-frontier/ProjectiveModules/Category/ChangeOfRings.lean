/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.ULift

/-!
# Lifted regular modules under restriction of scalars

A ring equivalence identifies the restriction of the target regular module with
the source regular module. When the rings lie in independent universes, lifting
both regular modules to the common maximum makes this an isomorphism in one
module category.

`ModuleCat.restrictScalarsUliftIsoOfEquiv` constructs this comparison using the
usual restriction-of-scalars and `ULift` module structures. Its homomorphism sends
`x` to `ULift.up (e.symm x.down)`, and its inverse sends `x` to
`ULift.up (e x.down)`. For rings in the same universe, the down-projection lemmas
identify both maps with Mathlib's `ModuleCat.restrictScalarsIsoOfEquiv`.

## References

* Mathlib's change-of-rings formalization by Jujian Zhang, including
  `ModuleCat.restrictScalarsIsoOfEquiv`.
* Mathlib's `ULift` module structures and linear equivalence by Kim Morrison.
-/

@[expose] public section

universe uR uS uM

open CategoryTheory

namespace ModuleCat

section

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Restriction of the lifted target regular module along a ring equivalence is
isomorphic to the lifted source regular module, with independent ring universes. -/
noncomputable def restrictScalarsUliftIsoOfEquiv (e : R ≃+* S) :
    (restrictScalars.{max uR uS} e.toRingHom).obj (of S (ULift.{uR} S)) ≅
      of R (ULift.{uS} R) :=
  LinearEquiv.toModuleIso
    (X₁ := (restrictScalars.{max uR uS} e.toRingHom).obj (of S (ULift.{uR} S)))
    (X₂ := of R (ULift.{uS} R))
    -- Retain the bundled restricted action when the carrier reduces to `ULift S`.
    (m₁ := ((restrictScalars.{max uR uS} e.toRingHom).obj
      (of S (ULift.{uR} S))).isModule)
    { toFun := fun x ↦ ULift.up (e.symm x.down)
      invFun := fun x ↦ ULift.up (e x.down)
      left_inv := fun x ↦ by
        apply ULift.ext
        exact e.apply_symm_apply x.down
      right_inv := fun x ↦ by
        apply ULift.ext
        exact e.symm_apply_apply x.down
      map_add' := fun x y ↦ by
        apply ULift.ext
        exact e.symm.map_add x.down y.down
      map_smul' := fun r x ↦ by
        apply ULift.ext
        change e.symm (e r * x.down) = r * e.symm x.down
        simp only [map_mul, RingEquiv.symm_apply_apply] }

/-- The forward comparison applies the inverse ring equivalence under `ULift`. -/
@[simp]
theorem restrictScalarsUliftIsoOfEquiv_hom_apply (e : R ≃+* S) (x : ULift.{uR} S) :
    (restrictScalarsUliftIsoOfEquiv e).hom x = ULift.up (e.symm x.down) :=
  rfl

/-- The inverse comparison applies the ring equivalence under `ULift`. -/
@[simp]
theorem restrictScalarsUliftIsoOfEquiv_inv_apply (e : R ≃+* S) (x : ULift.{uS} R) :
    (restrictScalarsUliftIsoOfEquiv e).inv x = ULift.up (e x.down) :=
  rfl

end

section

variable {R S : Type uR} [Ring R] [Ring S]

/-- In a common ring universe, the forward lifted comparison agrees under
`ULift.down` with the regular-module comparison. -/
theorem restrictScalarsUliftIsoOfEquiv_hom_down (e : R ≃+* S) (x : ULift.{uR} S) :
    ((restrictScalarsUliftIsoOfEquiv e).hom x).down =
      (restrictScalarsIsoOfEquiv e).hom x.down := by
  calc
    _ = e.symm x.down :=
      congrArg (ULift.down : ULift.{uR} R → R)
        (restrictScalarsUliftIsoOfEquiv_hom_apply e x)
    _ = _ := (restrictScalarsIsoOfEquiv_hom_apply e x.down).symm

/-- In a common ring universe, the inverse lifted comparison agrees under
`ULift.down` with the inverse regular-module comparison. -/
theorem restrictScalarsUliftIsoOfEquiv_inv_down (e : R ≃+* S) (x : ULift.{uR} R) :
    ((restrictScalarsUliftIsoOfEquiv e).inv x).down =
      (restrictScalarsIsoOfEquiv e).inv x.down := by
  exact (congrArg (ULift.down : ULift.{uR} S → S)
    (restrictScalarsUliftIsoOfEquiv_inv_apply e x)).trans
      (restrictScalarsIsoOfEquiv_inv_apply e x.down).symm

end

/-- For the identity ring equivalence, the lifted regular-module comparison is
the restriction-by-identity comparison on the lifted regular module. -/
theorem restrictScalarsUliftIsoOfEquiv_refl (R : Type uR) [Ring R] :
    restrictScalarsUliftIsoOfEquiv (RingEquiv.refl R) =
      restrictScalarsId'App (RingHom.id R) rfl (of R (ULift.{uR} R)) := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  calc
    _ = x.down :=
      congrArg (ULift.down : ULift.{uR} R → R)
        (restrictScalarsUliftIsoOfEquiv_hom_apply (RingEquiv.refl R) x)
    _ = _ :=
      (congrArg (ULift.down : ULift.{uR} R → R)
        (restrictScalarsId'App_hom_apply (RingHom.id R) rfl
          (of R (ULift.{uR} R)) x)).symm

/-- Restriction along a surjective ring homomorphism preserves the endomorphism
ring. Both directions leave the underlying additive map unchanged. -/
noncomputable def restrictScalarsEndEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{uM} S) :
    Module.End S M ≃+* Module.End R ((restrictScalars f).obj M) where
  toFun g := ((restrictScalars f).map (ofHom (X := M) (Y := M) g)).hom
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun s m ↦ by
        obtain ⟨r, rfl⟩ := hf s
        exact g.map_smul r m }
  left_inv _ := LinearMap.ext fun _ ↦ rfl
  right_inv _ := LinearMap.ext fun _ ↦ rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Restriction does not change the values of an endomorphism. -/
@[simp]
theorem restrictScalarsEndEquiv_apply {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{uM} S)
    (g : Module.End S M) (x : M) :
    restrictScalarsEndEquiv f hf M g x = g x := rfl

/-- The inverse endomorphism correspondence leaves values unchanged as well. -/
@[simp]
theorem restrictScalarsEndEquiv_symm_apply {R : Type uR} {S : Type uS}
    [Ring R] [Ring S] (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{uM} S)
    (g : Module.End R ((restrictScalars f).obj M)) (x : M) :
    (restrictScalarsEndEquiv f hf M).symm g x = g x := rfl

end ModuleCat
