/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Copyright (c) 2023 Heather Macbeth. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Adapted from mathlib work by Kim Morrison, Andrew Yang, Johan Commelin,
Heather Macbeth, Adam Topaz and other mathlib contributors; see the module documentation.
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Algebra.Field

/-!
# Continuous functions as ringed and locally ringed spaces

The sheaf of continuous functions into a topological commutative ring has an evaluation
homomorphism from each stalk and defines a ringed space. Continuous maps induce morphisms
of ringed spaces, with the opposite direction on stalks. For a topological field with closed
points, evaluation detects units and makes this a locally ringed space.

The sheaf and evaluation constructions are based on the work of Kim Morrison and Andrew Yang
on continuous-function presheaves. The stalk and locally ringed space arguments adapt the
smooth-manifold construction of Heather Macbeth, and the generic sheaf-of-functions work of
Adam Topaz and other mathlib contributors.

## References

* Mathlib, `Mathlib/Topology/Sheaves/CommRingCat.lean` (Kim Morrison and Andrew Yang):
  continuous-function presheaves of commutative rings. The sheaf property of
  `ContinuousFunctions.sheaf` is proved in this library.
* Mathlib, `Mathlib/Topology/Sheaves/LocalPredicate.lean` (Johan Commelin, Kim Morrison
  and Adam Topaz): the separate local-predicate sheaf construction, including the
  type-valued continuous-function sheaf used in the proof above.
* Mathlib, `Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean` (Heather Macbeth):
  the stalk-unit and local-ring method adapted to continuous functions.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Definition 4.3.9 (p. 142): continuous real-function sheaves on local
  balls motivate the model. Arbitrary topological commutative-ring coefficients
  and the sheaf proof here are project work; field-valued local stalks require
  `T1Space`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite AlgebraicGeometry

universe u

namespace ContinuousFunctions

variable (X : Type u) [TopologicalSpace X]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Continuous `R`-valued functions on the open subsets of `X`, as a sheaf of rings. -/
@[implicit_reducible]
def sheaf : (TopCat.of X).Sheaf CommRingCat.{u} where
  obj := TopCat.presheafToTopCommRing (TopCat.of X) (TopCommRingCat.of R)
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (TopCat.sheafToTop (X := TopCat.of X) (TopCat.of R)).property

instance coeFun (U : (Opens (TopCat.of X))ᵒᵖ) :
    CoeFun ((sheaf X R).presheaf.obj U) (fun _ => U.unop → R) where
  coe s := s.1

/-- The commutative ring of germs of continuous `R`-valued functions at `x`. -/
abbrev stalk (x : X) : Type u := (sheaf X R).presheaf.stalk x

/-- Evaluation of a section defined on a neighborhood of `x`. -/
def evalAt (x : X) (U : OpenNhds (x : TopCat.of X)) :
    (sheaf X R).presheaf.obj (op U.1) ⟶ CommRingCat.of R :=
  CommRingCat.ofHom
    { toFun := fun s => s ⟨x, U.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Evaluation of sections on neighborhoods of `x` forms a cocone of ring homomorphisms. -/
def evalCocone (x : X) :
    Cocone ((OpenNhds.inclusion (x : TopCat.of X)).op ⋙ (sheaf X R).presheaf) where
  pt := CommRingCat.of R
  ι := { app U := evalAt X R x U.unop
         naturality := by cat_disch }

/-- Evaluation of continuous germs at their base point, as a ring morphism. -/
def evalHom (x : X) : (sheaf X R).presheaf.stalk x ⟶ CommRingCat.of R :=
  colimit.desc _ (evalCocone X R x)

/-- Evaluation of continuous germs at their base point. -/
def eval (x : X) : stalk X R x →+* R := (evalHom X R x).hom

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc, elementwise]
theorem ι_evalHom (x : X) (U) :
    colimit.ι ((OpenNhds.inclusion (x : TopCat.of X)).op ⋙
      (sheaf X R).presheaf) U ≫ evalHom X R x = evalAt X R x (unop U) :=
  by
    change colimit.ι _ U ≫ colimit.desc _ (evalCocone X R x) =
      (evalCocone X R x).ι.app U
    exact colimit.ι_desc _ _

/-- The value of a germ is the value of any representative at the base point. -/
@[simp]
theorem eval_germ (U : Opens X) (x : X) (hx : x ∈ U)
    (s : (sheaf X R).presheaf.obj (op U)) :
    eval X R x ((sheaf X R).presheaf.germ U x hx s) = s ⟨x, hx⟩ :=
  congrArg (fun h => h s) (ι_evalHom X R x ⟨U, hx⟩)

/-- The ring-category version of evaluation on a representative. -/
@[simp]
theorem evalHom_germ (U : Opens X) (x : X) (hx : x ∈ U)
    (s : (sheaf X R).presheaf.obj (op U)) :
    evalHom X R x ((sheaf X R).presheaf.germ U x hx s) = s ⟨x, hx⟩ :=
  eval_germ X R U x hx s

/-- Every ring element is the value of a constant germ. -/
theorem eval_surjective (x : X) : Function.Surjective (eval X R x) := by
  intro value
  let constant : (sheaf X R).presheaf.obj (op (⊤ : Opens X)) :=
    TopCat.ofHom ⟨fun _ => value, continuous_const⟩
  refine ⟨(sheaf X R).presheaf.germ ⊤ x (by simp) constant, ?_⟩
  rw [eval_germ]
  rfl

instance [Nontrivial R] (x : X) : Nontrivial (stalk X R x) :=
  (eval_surjective X R x).nontrivial

variable (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T1Space K]

set_option backward.isDefEq.respectTransparency false in
/-- A continuous germ into a topological field is invertible exactly when its value is nonzero.
The local inverse argument adapts Heather Macbeth's smooth-sheaf stalk-unit proof in Mathlib. -/
theorem isUnit_stalk_iff (x : X) (s : stalk X K x) :
    IsUnit s ↔ eval X K x s ≠ 0 := by
  constructor
  · intro hs
    exact (isUnit_iff_ne_zero.mp (hs.map (eval X K x)))
  · intro hs
    let S := (sheaf X K).presheaf
    obtain ⟨U, hxU, representative, rfl⟩ := S.exists_germ_eq s
    let fieldSection : C(U, K) := representative.hom
    have hsection : fieldSection ⟨x, hxU⟩ ≠ 0 := by
      change representative ⟨x, hxU⟩ ≠ 0
      rw [← eval_germ X K U x hxU representative]
      exact hs
    have hne : ∀ᶠ (point : U) in 𝓝 ⟨x, hxU⟩, fieldSection point ≠ 0 :=
      fieldSection.continuous.continuousAt.eventually_ne hsection
    rw [eventually_nhds_iff] at hne
    obtain ⟨V₀, hV₀f, hV₀, hxV₀⟩ := hne
    let V : Opens X := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀⟩
    have hVU : V ≤ U := Subtype.coe_image_subset (U : Set X) V₀
    have hV : V₀ = Set.range (Set.inclusion hVU) := by
      convert (Set.range_inclusion hVU).symm
      ext point
      change _ ↔ point ∈ Subtype.val ⁻¹' Subtype.val '' V₀
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV
    have hxV : x ∈ (V : Set X) := by
      obtain ⟨point, hp⟩ := hxV₀
      convert point.2
      exact congrArg Subtype.val hp.symm
    have hnonzero : ∀ point : V, fieldSection (Set.inclusion hVU point) ≠ 0 :=
      fun point => hV₀f (Set.inclusion hVU point) (Set.mem_range_self point)
    let inverse : (sheaf X K).presheaf.obj (op V) :=
      TopCat.ofHom ⟨fun point : V => (fieldSection (Set.inclusion hVU point))⁻¹,
        (fieldSection.continuous.comp (by fun_prop)).inv₀ hnonzero⟩
    refine ⟨⟨S.germ V x hxV (S.map (homOfLE hVU).op representative),
      S.germ V x hxV inverse, ?_, ?_⟩,
      S.germ_res_apply (homOfLE hVU) x hxV representative⟩
    · rw [← map_mul]
      convert RingHom.map_one _
      apply TopCat.ext
      intro point
      exact mul_inv_cancel₀ (hnonzero point)
    · rw [← map_mul]
      convert RingHom.map_one _
      apply TopCat.ext
      intro point
      exact inv_mul_cancel₀ (hnonzero point)

/-- The nonunits in a stalk are exactly the germs that vanish at the base point. -/
theorem nonunits_stalk (x : X) :
    nonunits (stalk X K x) = RingHom.ker (eval X K x) := by
  ext s
  rw [mem_nonunits_iff]
  change ¬ IsUnit s ↔ eval X K x s = 0
  simp only [isUnit_stalk_iff X K x s, not_ne_iff]

/-- Stalks of continuous field-valued functions are local rings. -/
instance instLocalRingStalk (x : X) : IsLocalRing (stalk X K x) := by
  apply IsLocalRing.of_nonunits_add
  rw [nonunits_stalk X K x]
  intro s t
  exact Ideal.add_mem _

variable (Y : Type u) [TopologicalSpace Y]

/-- The inverse image of an open set along a continuous function, viewed as a topological space. -/
abbrev inverseImage (f : X → Y) (hf : Continuous f) (U : Opens Y) : Opens X :=
  (Opens.map (TopCat.ofHom ⟨f, hf⟩)).obj U

/-- Precomposition of continuous functions on open sets. -/
def precompose (f : X → Y) (hf : Continuous f) (U : Opens Y) :
    (sheaf Y R).presheaf.obj (op U) →+*
      (sheaf X R).presheaf.obj (op (inverseImage X Y f hf U)) where
  toFun representative :=
    TopCat.ofHom ⟨fun point => representative ⟨f point.1, point.2⟩,
      representative.hom.continuous.comp (Continuous.subtype_mk (hf.comp continuous_subtype_val) _)⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-- Pulling back a section evaluates it after applying the base-space map. -/
@[simp]
theorem precompose_apply (f : X → Y) (hf : Continuous f) (U : Opens Y)
    (s : (sheaf Y R).presheaf.obj (op U)) (point : inverseImage X Y f hf U) :
    precompose X R Y f hf U s point = s ⟨f point.1, point.2⟩ :=
  rfl

/-- The sheaf morphism induced by precomposition with a continuous function. -/
def sheafHom (f : X → Y) (hf : Continuous f) :
    sheaf Y R ⟶
      (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf⟩)).obj (sheaf X R) where
  hom.app U := CommRingCat.ofHom (precompose X R Y f hf U.unop)
  hom.naturality := by
    intro U V inclusion
    ext representative
    rfl

/-- The ringed space of continuous functions with values in a topological commutative ring. -/
@[implicit_reducible]
def ringedSpace : RingedSpace where
  carrier := TopCat.of X
  presheaf := (sheaf X R).presheaf
  IsSheaf := (sheaf X R).property

/-- A continuous map induces a morphism of ringed spaces by precomposition. -/
def ringedSpaceMap (f : X → Y) (hf : Continuous f) :
    ringedSpace X R ⟶ ringedSpace Y R :=
  InducedCategory.homMk {
    base := TopCat.ofHom ⟨f, hf⟩
    c := (sheafHom X R Y f hf).hom }

/-- Pullback of a continuous germ preserves evaluation at its base point. -/
@[reassoc (attr := simp)]
theorem ringedSpaceMap_stalkMap_evalHom (f : X → Y) (hf : Continuous f) (x : X) :
    (ringedSpaceMap X R Y f hf).hom.stalkMap x ≫ evalHom X R x =
      evalHom Y R (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext representative
  exact (evalHom_germ X R _ _ _ _).trans (evalHom_germ Y R _ _ _ _).symm

/-- Pullback of a germ is the germ of the precomposed section. -/
@[simp]
theorem ringedSpaceMap_stalkMap_germ (f : X → Y) (hf : Continuous f)
    (U : Opens Y) (x : X) (hx : f x ∈ U)
    (s : (sheaf Y R).presheaf.obj (op U)) :
    (ringedSpaceMap X R Y f hf).hom.stalkMap x
      ((sheaf Y R).presheaf.germ U (f x) hx s) =
    (sheaf X R).presheaf.germ (inverseImage X Y f hf U) x hx
      (precompose X R Y f hf U s) :=
  PresheafedSpace.stalkMap_germ_apply (ringedSpaceMap X R Y f hf).hom U x hx s

/-- Identity maps induce identity morphisms of ringed spaces. -/
theorem ringedSpaceMap_id :
    ringedSpaceMap X R X id continuous_id = 𝟙 (ringedSpace X R) := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

/-- Composition of continuous maps induces composition of ringed-space morphisms. -/
theorem ringedSpaceMap_comp (Z : Type u) [TopologicalSpace Z]
    (f : X → Y) (hf : Continuous f) (g : Y → Z) (hg : Continuous g) :
    ringedSpaceMap X R Z (g ∘ f) (hg.comp hf) =
      ringedSpaceMap X R Y f hf ≫ ringedSpaceMap Y R Z g hg := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

/-- The locally ringed space of continuous functions with values in `K`. -/
@[implicit_reducible]
def locallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of X
  presheaf := (sheaf X K).presheaf
  IsSheaf := (sheaf X K).property
  isLocalRing x := instLocalRingStalk X K x

/-- The underlying morphism of presheafed spaces for a continuous function. -/
def locallyRingedSpaceMapAux (f : X → Y) (hf : Continuous f) :
    (locallyRingedSpace X K).toPresheafedSpace ⟶
      (locallyRingedSpace Y K).toPresheafedSpace where
  base := TopCat.ofHom ⟨f, hf⟩
  c := (sheafHom X K Y f hf).hom

/-- Evaluation commutes with pullback of germs along a continuous function. -/
theorem stalkMap_evalHom_aux (f : X → Y) (hf : Continuous f) (x : X) :
    (locallyRingedSpaceMapAux X K Y f hf).stalkMap x ≫ evalHom X K x =
      evalHom Y K (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext representative
  exact (evalHom_germ X K _ _ _ _).trans (evalHom_germ Y K _ _ _ _).symm

/-- A continuous function induces an actual morphism of locally ringed spaces. -/
def locallyRingedSpaceMap (f : X → Y) (hf : Continuous f) :
    locallyRingedSpace X K ⟶ locallyRingedSpace Y K where
  __ := locallyRingedSpaceMapAux X K Y f hf
  prop x := by
    refine ⟨fun representative hsection => ?_⟩
    rw [isUnit_stalk_iff] at hsection
    rw [isUnit_stalk_iff]
    exact (congrArg (fun hom => hom representative) (stalkMap_evalHom_aux X K Y f hf x)).symm ▸
      hsection

/-- Forgetting locality identifies the field-valued map with the general ringed-space map. -/
theorem forget_locallyRingedSpaceMap (f : X → Y) (hf : Continuous f) :
    LocallyRingedSpace.forgetToSheafedSpace.map (locallyRingedSpaceMap X K Y f hf) =
      ringedSpaceMap X K Y f hf :=
  rfl

/-- The stalk arrow on a continuous map commutes with evaluation. -/
@[reassoc (attr := simp)]
theorem stalkMap_evalHom (f : X → Y) (hf : Continuous f) (x : X) :
    (locallyRingedSpaceMap X K Y f hf).stalkMap x ≫ evalHom X K x =
      evalHom Y K (f x) :=
  stalkMap_evalHom_aux X K Y f hf x

/-- Pullback of a germ is the germ of the section pulled back to the inverse-image open set. -/
@[simp]
theorem stalkMap_germ (f : X → Y) (hf : Continuous f) (U : Opens Y)
    (x : X) (hx : f x ∈ U) (s : (sheaf Y K).presheaf.obj (op U)) :
    (locallyRingedSpaceMap X K Y f hf).stalkMap x
      ((sheaf Y K).presheaf.germ U (f x) hx s) =
    (sheaf X K).presheaf.germ (inverseImage X Y f hf U) x hx
      (precompose X K Y f hf U s) :=
  LocallyRingedSpace.stalkMap_germ_apply (locallyRingedSpaceMap X K Y f hf) U x hx s

/-- The stalk arrow for a continuous map is a local ring homomorphism. -/
theorem stalkMap_isLocalHom (f : X → Y) (hf : Continuous f) (x : X) :
    IsLocalHom ((locallyRingedSpaceMap X K Y f hf).stalkMap x).hom :=
  (locallyRingedSpaceMap X K Y f hf).prop x

/-- Identity functions induce identity morphisms of locally ringed spaces. -/
theorem locallyRingedSpaceMap_id :
    locallyRingedSpaceMap X K X id continuous_id = 𝟙 (locallyRingedSpace X K) := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

/-- Composition of continuous functions induces composition of locally ringed-space maps. -/
theorem locallyRingedSpaceMap_comp (Z : Type u) [TopologicalSpace Z]
    (f : X → Y) (hf : Continuous f) (g : Y → Z) (hg : Continuous g) :
    locallyRingedSpaceMap X K Z (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap X K Y f hf ≫ locallyRingedSpaceMap Y K Z g hg := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

end ContinuousFunctions
end
