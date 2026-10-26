/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.SingleCoverExtension
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Group objects extended from one-cover-dense subfunctors

The pointwise product of subfunctors has a carrier canonically isomorphic to the product
of their carriers. For a one-cover-dense subfunctor with a group-object structure,
singleton descent of its ambient presheaf determines a group-object structure on that
exact presheaf. The multiplication, unit and inversion restrict to those of the
subfunctor, and the resulting structure is unique with this property.

Unlike the finite-type-scheme statement motivating this construction, the category
of tests need only admit the pullbacks required by the covering morphisms; no
representability or Grothendieck topology is assumed. The represented-scheme
specialization requires a separate comparison with the functor of points.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 5.12, for the motivating
  represented-scheme statement.
- Scheme Properties' single-cover extension and product-density theorems.
- Mathlib's `Subfunctor`, `GrpObj` and Cartesian product infrastructure.
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

universe v u w

namespace CategoryTheory.CartesianMonoidalCategory

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K]
  [HasBinaryProducts K]

/-- The canonical chosen-product-to-tensor comparison preserves the first projection. -/
@[reassoc (attr := simp)]
theorem tensorLeftIsoProd_inv_app_fst (A B : K) :
    (tensorLeftIsoProd A).inv.app B ≫ fst A B = prod.fst :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_inv_comp
    (limit.isLimit _) ⟨.left⟩

/-- The canonical chosen-product-to-tensor comparison preserves the second projection. -/
@[reassoc (attr := simp)]
theorem tensorLeftIsoProd_inv_app_snd (A B : K) :
    (tensorLeftIsoProd A).inv.app B ≫ snd A B = prod.snd :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_inv_comp
    (limit.isLimit _) ⟨.right⟩

/-- The tensor-to-chosen-product comparison preserves the first projection. -/
@[reassoc (attr := simp)]
theorem tensorLeftIsoProd_hom_app_fst (A B : K) :
    (tensorLeftIsoProd A).hom.app B ≫ prod.fst = fst A B :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) ⟨.left⟩

/-- The tensor-to-chosen-product comparison preserves the second projection. -/
@[reassoc (attr := simp)]
theorem tensorLeftIsoProd_hom_app_snd (A B : K) :
    (tensorLeftIsoProd A).hom.app B ≫ prod.snd = snd A B :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) ⟨.right⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison is natural in both tensor factors. -/
theorem tensorLeftIsoProd_inv_app_map {A B A' B' : K}
    (f : A ⟶ A') (g : B ⟶ B') :
    prod.map f g ≫ (tensorLeftIsoProd A').inv.app B' =
      (tensorLeftIsoProd A).inv.app B ≫ (f ⊗ₘ g) := by
  apply hom_ext
  · simp only [Category.assoc, tensorLeftIsoProd_inv_app_fst,
      tensorLeftIsoProd_inv_app_fst_assoc, prod.map_fst, tensorHom_fst]
  · simp only [Category.assoc, tensorLeftIsoProd_inv_app_snd,
      tensorLeftIsoProd_inv_app_snd_assoc, prod.map_snd, tensorHom_snd]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse canonical comparison is natural in both tensor factors. -/
theorem tensorLeftIsoProd_hom_app_map {A B A' B' : K}
    (f : A ⟶ A') (g : B ⟶ B') :
    (tensorLeftIsoProd A).hom.app B ≫ prod.map f g =
      (f ⊗ₘ g) ≫ (tensorLeftIsoProd A').hom.app B' := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst]
    conv_rhs => erw [tensorLeftIsoProd_hom_app_fst, tensorHom_fst]
    simpa only [Category.assoc] using
      congrArg (fun h : A ⊗ B ⟶ A => h ≫ f) (tensorLeftIsoProd_hom_app_fst A B)
  · simp only [Category.assoc, prod.map_snd]
    conv_rhs => erw [tensorLeftIsoProd_hom_app_snd, tensorHom_snd]
    simpa only [Category.assoc] using
      congrArg (fun h : A ⊗ B ⟶ B => h ≫ g) (tensorLeftIsoProd_hom_app_snd A B)

end CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type w}

/-- The first subtype-valued projection of a product subfunctor. -/
noncomputable def productFst (D : Subfunctor F) (E : Subfunctor G) :
    (D.product E).toFunctor ⟶ D.toFunctor where
  app X := ↾fun x => ⟨(prod.fst : F ⨯ G ⟶ F).app X x.1,
    (D.mem_product_iff E X x.1).mp x.2 |>.1⟩
  naturality X Y f := by
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply (prod.fst : F ⨯ G ⟶ F) f x.1

/-- The second subtype-valued projection of a product subfunctor. -/
noncomputable def productSnd (D : Subfunctor F) (E : Subfunctor G) :
    (D.product E).toFunctor ⟶ E.toFunctor where
  app X := ↾fun x => ⟨(prod.snd : F ⨯ G ⟶ G).app X x.1,
    (D.mem_product_iff E X x.1).mp x.2 |>.2⟩
  naturality X Y f := by
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply (prod.snd : F ⨯ G ⟶ G) f x.1

/-- The first carrier projection followed by inclusion is the ambient projection. -/
@[reassoc (attr := simp)]
theorem productFst_comp_ι (D : Subfunctor F) (E : Subfunctor G) :
    productFst D E ≫ D.ι = (D.product E).ι ≫ prod.fst := by
  ext X x
  rfl

/-- The second carrier projection followed by inclusion is the ambient projection. -/
@[reassoc (attr := simp)]
theorem productSnd_comp_ι (D : Subfunctor F) (E : Subfunctor G) :
    productSnd D E ≫ E.ι = (D.product E).ι ≫ prod.snd := by
  ext X x
  rfl

/-- The map back from the product of the carrier functors. -/
noncomputable def productPair (D : Subfunctor F) (E : Subfunctor G) :
    D.toFunctor ⨯ E.toFunctor ⟶ (D.product E).toFunctor where
  app X := ↾fun x => ⟨(prod.map D.ι E.ι).app X x, by
    rw [D.mem_product_iff E]
    constructor
    · change ((prod.map D.ι E.ι ≫ prod.fst).app X x) ∈ D.obj X
      rw [prod.map_fst]
      exact ((prod.fst : D.toFunctor ⨯ E.toFunctor ⟶ D.toFunctor).app X x).2
    · change ((prod.map D.ι E.ι ≫ prod.snd).app X x) ∈ E.obj X
      rw [prod.map_snd]
      exact ((prod.snd : D.toFunctor ⨯ E.toFunctor ⟶ E.toFunctor).app X x).2⟩
  naturality X Y f := by
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply (prod.map D.ι E.ι) f x

/-- Pairing the subtype-valued sections and then including forgets their membership proofs. -/
@[reassoc (attr := simp)]
theorem productPair_comp_ι (D : Subfunctor F) (E : Subfunctor G) :
    productPair D E ≫ (D.product E).ι = prod.map D.ι E.ι := rfl

/-- The carrier of the product subfunctor is the chosen product of the carriers.
This does not identify chosen products definitionally. -/
noncomputable def productIso (D : Subfunctor F) (E : Subfunctor G) :
    (D.product E).toFunctor ≅ D.toFunctor ⨯ E.toFunctor where
  hom := prod.lift (productFst D E) (productSnd D E)
  inv := productPair D E
  hom_inv_id := by
    apply (cancel_mono (D.product E).ι).1
    rw [Category.assoc, productPair_comp_ι, prod.lift_map,
      productFst_comp_ι, productSnd_comp_ι, ← prod.comp_lift]
    simp
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst]
      apply (cancel_mono D.ι).1
      rw [Category.assoc, productFst_comp_ι, ← Category.assoc,
        productPair_comp_ι, prod.map_fst]
      simp
    · rw [Category.assoc, prod.lift_snd]
      apply (cancel_mono E.ι).1
      rw [Category.assoc, productSnd_comp_ι, ← Category.assoc,
        productPair_comp_ι, prod.map_snd]
      simp

/-- The comparison's first projection. -/
@[reassoc (attr := simp)]
theorem productIso_hom_fst (D : Subfunctor F) (E : Subfunctor G) :
    (productIso D E).hom ≫ prod.fst = productFst D E :=
  prod.lift_fst _ _

/-- The comparison's second projection. -/
@[reassoc (attr := simp)]
theorem productIso_hom_snd (D : Subfunctor F) (E : Subfunctor G) :
    (productIso D E).hom ≫ prod.snd = productSnd D E :=
  prod.lift_snd _ _

/-- Comparing carriers and then including them equals the product inclusion. -/
@[reassoc (attr := simp)]
theorem productIso_hom_comp_map_ι (D : Subfunctor F) (E : Subfunctor G) :
    (productIso D E).hom ≫ prod.map D.ι E.ι = (D.product E).ι := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc,
      productIso_hom_fst, productFst_comp_ι]
  · rw [Category.assoc, prod.map_snd, ← Category.assoc,
      productIso_hom_snd, productSnd_comp_ι]

/-- The associator for the carrier of three product subfunctors. -/
noncomputable def productAssoc (D : Subfunctor F) (E : Subfunctor G)
    (T : Subfunctor H) :
    ((D.product E).product T).toFunctor ≅ (D.product (E.product T)).toFunctor :=
  productIso (D.product E) T ≪≫
    prod.mapIso (productIso D E) (Iso.refl T.toFunctor) ≪≫
      prod.associator D.toFunctor E.toFunctor T.toFunctor ≪≫
        prod.mapIso (Iso.refl D.toFunctor) (productIso E T).symm ≪≫
          (productIso D (E.product T)).symm

/-- The two bracketings of the carrier comparison agree with the product associator. -/
theorem productIso_assoc (D : Subfunctor F) (E : Subfunctor G)
    (T : Subfunctor H) :
    (productAssoc D E T).hom ≫ (productIso D (E.product T)).hom ≫
      prod.map (𝟙 D.toFunctor) (productIso E T).hom =
    (productIso (D.product E) T).hom ≫
      prod.map (productIso D E).hom (𝟙 T.toFunctor) ≫
        (prod.associator D.toFunctor E.toFunctor T.toFunctor).hom := by
  simp only [productAssoc, Iso.trans_hom, Iso.symm_hom, prod.mapIso_hom]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem productIso_tensorLeftIsoProd_hom_ι (D : Subfunctor F) (E : Subfunctor G) :
    (D.product E).ι ≫
      (((CartesianMonoidalCategory.tensorLeftIsoProd F).symm).app G).hom =
      (productIso D E).hom ≫
        (((CartesianMonoidalCategory.tensorLeftIsoProd D.toFunctor).symm).app
          E.toFunctor).hom ≫
        (D.ι ⊗ₘ E.ι) := by
  simp only [Iso.app_hom, Iso.symm_hom]
  erw [← productIso_hom_comp_map_ι D E, Category.assoc,
    CartesianMonoidalCategory.tensorLeftIsoProd_inv_app_map]

variable {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
  [W.IsStableUnderComposition] {D : Subfunctor F} [GrpObj D.toFunctor]

/-- Extend the multiplication of a one-cover-dense group-valued subfunctor. -/
noncomputable def mulExtension (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) : F ⊗ F ⟶ F :=
  (((CartesianMonoidalCategory.tensorLeftIsoProd F).symm).app F).inv ≫
    extendOneCover (hD.product hD) hF
      ((productIso D D).hom ≫
        (((CartesianMonoidalCategory.tensorLeftIsoProd D.toFunctor).symm).app
          D.toFunctor).hom ≫
        MonObj.mul (X := D.toFunctor) ≫ D.ι)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The extended multiplication agrees with the original multiplication on the subfunctor. -/
theorem mulExtension_restrict (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    (D.ι ⊗ₘ D.ι) ≫ mulExtension hD hF =
      MonObj.mul (X := D.toFunctor) ≫ D.ι := by
  unfold mulExtension
  simp only [Iso.app_inv, Iso.symm_inv]
  with_unfolding_all
    erw [← Category.assoc,
      ← CartesianMonoidalCategory.tensorLeftIsoProd_hom_app_map]
  simp only [Category.assoc, ← productPair_comp_ι D D]
  rw [← Category.assoc, ι_comp_extendOneCover]
  change (((CartesianMonoidalCategory.tensorLeftIsoProd D.toFunctor).symm).app
      D.toFunctor).inv ≫
      (productIso D D).inv ≫ (productIso D D).hom ≫
        (((CartesianMonoidalCategory.tensorLeftIsoProd D.toFunctor).symm).app
          D.toFunctor).hom ≫
          MonObj.mul (X := D.toFunctor) ≫ D.ι = _
  simp

omit [GrpObj D.toFunctor] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorRestriction_injective (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    Function.Injective (fun φ : F ⊗ F ⟶ F => (D.ι ⊗ₘ D.ι) ≫ φ) := by
  intro φ ψ hφψ
  change (D.ι ⊗ₘ D.ι) ≫ φ = (D.ι ⊗ₘ D.ι) ≫ ψ at hφψ
  apply (cancel_epi
    (((CartesianMonoidalCategory.tensorLeftIsoProd F).symm).app F).hom).1
  apply (oneCoverExtensionEquiv (hD.product hD) hF).injective
  simp only [oneCoverExtensionEquiv_apply]
  have hcomparison : (D.product D).ι ≫
      (((CartesianMonoidalCategory.tensorLeftIsoProd F).symm).app F).hom =
      (productIso D D).hom ≫
        (((CartesianMonoidalCategory.tensorLeftIsoProd D.toFunctor).symm).app
          D.toFunctor).hom ≫
        (D.ι ⊗ₘ D.ι) := by
    exact productIso_tensorLeftIsoProd_hom_ι D D
  conv_lhs => rw [← Category.assoc, hcomparison]
  conv_rhs => rw [← Category.assoc, hcomparison]
  simp only [Category.assoc, hφψ]

omit [W.IsStableUnderComposition] [GrpObj D.toFunctor] in
/-- Restricting maps out of the tensor unit and a presheaf to a one-cover-dense
subfunctor is injective when the target satisfies singleton descent. -/
theorem leftTensorRestriction_injective
    (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    Function.Injective (fun φ : (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ F ⟶ F =>
      (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ φ) := by
  intro φ ψ hφψ
  change (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ φ =
    (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ ψ at hφψ
  apply (cancel_epi (λ_ F).inv).1
  apply (oneCoverExtensionEquiv hD hF).injective
  simp only [oneCoverExtensionEquiv_apply]
  simpa only [← Category.assoc, id_tensorHom,
    ← leftUnitor_inv_naturality D.ι] using
      congrArg (fun θ : (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ D.toFunctor ⟶ F =>
        (λ_ D.toFunctor).inv ≫ θ) hφψ

omit [W.IsStableUnderComposition] [GrpObj D.toFunctor] in
/-- Restricting maps out of a presheaf and the tensor unit to a one-cover-dense
subfunctor is injective when the target satisfies singleton descent. -/
theorem rightTensorRestriction_injective
    (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    Function.Injective (fun φ : F ⊗ (𝟙_ (Cᵒᵖ ⥤ Type w)) ⟶ F =>
      (D.ι ⊗ₘ 𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w))) ≫ φ) := by
  intro φ ψ hφψ
  change (D.ι ⊗ₘ 𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w))) ≫ φ =
    (D.ι ⊗ₘ 𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w))) ≫ ψ at hφψ
  apply (cancel_epi (ρ_ F).inv).1
  apply (oneCoverExtensionEquiv hD hF).injective
  simp only [oneCoverExtensionEquiv_apply]
  simpa only [← Category.assoc, tensorHom_id,
    ← rightUnitor_inv_naturality D.ι] using
      congrArg (fun θ : D.toFunctor ⊗ (𝟙_ (Cᵒᵖ ⥤ Type w)) ⟶ F =>
        (ρ_ D.toFunctor).inv ≫ θ) hφψ

private noncomputable def tripleTensorIso (D : Subfunctor F) :
    ((D.product D).product D).toFunctor ≅
      (D.toFunctor ⊗ D.toFunctor) ⊗ D.toFunctor :=
  productIso (D.product D) D ≪≫
    (((CartesianMonoidalCategory.tensorLeftIsoProd (D.product D).toFunctor).symm).app
      D.toFunctor) ≪≫
      tensorIso (productIso D D ≪≫
          (((CartesianMonoidalCategory.tensorLeftIsoProd D.toFunctor).symm).app
            D.toFunctor))
        (Iso.refl D.toFunctor)

private noncomputable def ambientTripleIso (F : Cᵒᵖ ⥤ Type w) :
    (F ⨯ F) ⨯ F ≅ (F ⊗ F) ⊗ F :=
  (((CartesianMonoidalCategory.tensorLeftIsoProd (F ⨯ F)).symm).app F) ≪≫
    tensorIso (((CartesianMonoidalCategory.tensorLeftIsoProd F).symm).app F)
      (Iso.refl F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem tripleTensorIso_hom_ι (D : Subfunctor F) :
    ((D.product D).product D).ι ≫ (ambientTripleIso F).hom =
      (tripleTensorIso D).hom ≫ ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) := by
  simp only [ambientTripleIso, tripleTensorIso, Iso.trans_hom,
    tensorIso_hom, Iso.refl_hom]
  with_unfolding_all
    rw [← Category.assoc, productIso_tensorLeftIsoProd_hom_ι (D.product D) D]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    productIso_tensorLeftIsoProd_hom_ι D D]

omit [GrpObj D.toFunctor] in
/-- Restriction along a triple product of one-cover-dense subfunctors is injective
for maps into a presheaf satisfying singleton descent. -/
theorem tensorTripleRestriction_injective
    (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    Function.Injective (fun φ : (F ⊗ F) ⊗ F ⟶ F =>
      ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) ≫ φ) := by
  intro φ ψ hφψ
  change ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) ≫ φ =
    ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) ≫ ψ at hφψ
  apply (cancel_epi (ambientTripleIso F).hom).1
  apply (oneCoverExtensionEquiv ((hD.product hD).product hD) hF).injective
  simp only [oneCoverExtensionEquiv_apply]
  conv_lhs => rw [← Category.assoc, tripleTensorIso_hom_ι D]
  conv_rhs => rw [← Category.assoc, tripleTensorIso_hom_ι D]
  simp only [Category.assoc, hφψ]

/-- Extend a group law from a one-cover-dense subfunctor to its ambient presheaf.
Only the target is required to satisfy descent for singleton covers. Motivated
by Milne's *Algebraic Groups* (2017), Proposition 5.12, this result constructs
a law on the exact presheaf rather than on a represented group scheme. -/
@[instance_reducible]
noncomputable def IsOneCoverDense.grpObj (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) : GrpObj F := by
  refine { one := MonObj.one (X := D.toFunctor) ≫ D.ι
           mul := mulExtension hD hF
           inv := extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι)
           one_mul := ?_
           mul_one := ?_
           mul_assoc := ?_
           left_inv := ?_
           right_inv := ?_ }
  · apply leftTensorRestriction_injective hD hF
    have hpair :
        (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫
          ((MonObj.one (X := D.toFunctor) ≫ D.ι) ▷ F) =
        (MonObj.one (X := D.toFunctor) ▷ D.toFunctor) ≫
          (D.ι ⊗ₘ D.ι) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [id_tensorHom, id_whiskerLeft, comp_whiskerRight, Category.assoc,
          CartesianMonoidalCategory.whiskerRight_fst,
          CartesianMonoidalCategory.whiskerRight_fst_assoc,
          CartesianMonoidalCategory.leftUnitor_inv_fst_assoc,
          SemiCartesianMonoidalCategory.comp_toUnit_assoc,
          CartesianMonoidalCategory.tensorHom_fst]
        have hterminal : CartesianMonoidalCategory.toUnit
            ((𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ D.toFunctor) =
            CartesianMonoidalCategory.fst (𝟙_ (Cᵒᵖ ⥤ Type w)) D.toFunctor :=
          CartesianMonoidalCategory.toUnit_unique _ _
        rw [hterminal]
      · simp only [id_tensorHom, id_whiskerLeft, comp_whiskerRight, Category.assoc,
          CartesianMonoidalCategory.whiskerRight_snd,
          CartesianMonoidalCategory.leftUnitor_inv_snd, Category.comp_id,
          CartesianMonoidalCategory.tensorHom_snd,
          CartesianMonoidalCategory.whiskerRight_snd_assoc]
        rw [CartesianMonoidalCategory.leftUnitor_hom]
    calc
      (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫
          ((MonObj.one (X := D.toFunctor) ≫ D.ι) ▷ F) ≫
            mulExtension hD hF =
        (MonObj.one (X := D.toFunctor) ▷ D.toFunctor) ≫
          (D.ι ⊗ₘ D.ι) ≫ mulExtension hD hF := by
            rw [← Category.assoc, hpair, Category.assoc]
      _ = (MonObj.one (X := D.toFunctor) ▷ D.toFunctor) ≫
            MonObj.mul (X := D.toFunctor) ≫ D.ι := by
              simp only [mulExtension_restrict]
      _ = (λ_ D.toFunctor).hom ≫ D.ι := by rw [← Category.assoc, MonObj.one_mul]
      _ = (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ (λ_ F).hom := by
            simp
  · apply rightTensorRestriction_injective hD hF
    have hpair :
        (D.ι ⊗ₘ 𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w))) ≫
          (F ◁ (MonObj.one (X := D.toFunctor) ≫ D.ι)) =
        (D.toFunctor ◁ MonObj.one (X := D.toFunctor)) ≫
          (D.ι ⊗ₘ D.ι) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [tensorHom_id, whiskerRight_id, whiskerLeft_comp, Category.assoc,
          CartesianMonoidalCategory.whiskerLeft_fst,
          CartesianMonoidalCategory.rightUnitor_inv_fst, Category.comp_id,
          CartesianMonoidalCategory.tensorHom_fst,
          CartesianMonoidalCategory.whiskerLeft_fst_assoc]
        rw [CartesianMonoidalCategory.rightUnitor_hom]
      · simp only [tensorHom_id, whiskerRight_id, whiskerLeft_comp, Category.assoc,
          CartesianMonoidalCategory.whiskerLeft_snd,
          CartesianMonoidalCategory.whiskerLeft_snd_assoc,
          CartesianMonoidalCategory.rightUnitor_inv_snd_assoc,
          SemiCartesianMonoidalCategory.comp_toUnit_assoc,
          CartesianMonoidalCategory.tensorHom_snd]
        have hterminal : CartesianMonoidalCategory.toUnit
            (D.toFunctor ⊗ (𝟙_ (Cᵒᵖ ⥤ Type w))) =
            CartesianMonoidalCategory.snd D.toFunctor (𝟙_ (Cᵒᵖ ⥤ Type w)) :=
          CartesianMonoidalCategory.toUnit_unique _ _
        rw [hterminal]
    calc
      (D.ι ⊗ₘ 𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w))) ≫
          (F ◁ (MonObj.one (X := D.toFunctor) ≫ D.ι)) ≫
            mulExtension hD hF =
        (D.toFunctor ◁ MonObj.one (X := D.toFunctor)) ≫
          (D.ι ⊗ₘ D.ι) ≫ mulExtension hD hF := by
            rw [← Category.assoc, hpair, Category.assoc]
      _ = (D.toFunctor ◁ MonObj.one (X := D.toFunctor)) ≫
            MonObj.mul (X := D.toFunctor) ≫ D.ι := by
              simp only [mulExtension_restrict]
      _ = (ρ_ D.toFunctor).hom ≫ D.ι := by rw [← Category.assoc, MonObj.mul_one]
      _ = (D.ι ⊗ₘ 𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w))) ≫ (ρ_ F).hom := by
            simp
  · apply tensorTripleRestriction_injective hD hF
    have hmul := mulExtension_restrict hD hF
    have hleft :
        ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) ≫
          (mulExtension hD hF ▷ F) =
        (MonObj.mul (X := D.toFunctor) ▷ D.toFunctor) ≫
          (D.ι ⊗ₘ D.ι) := by
      calc
        _ = (((D.ι ⊗ₘ D.ι) ≫ mulExtension hD hF) ⊗ₘ
            (D.ι ≫ 𝟙 F)) := by rw [← tensorHom_id, tensorHom_comp_tensorHom]
        _ = ((MonObj.mul (X := D.toFunctor) ≫ D.ι) ⊗ₘ D.ι) := by
              rw [hmul, Category.comp_id]
        _ = _ := by rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
    have hright :
        (D.ι ⊗ₘ (D.ι ⊗ₘ D.ι)) ≫
          (F ◁ mulExtension hD hF) =
        (D.toFunctor ◁ MonObj.mul (X := D.toFunctor)) ≫
          (D.ι ⊗ₘ D.ι) := by
      calc
        _ = (D.ι ≫ 𝟙 F) ⊗ₘ
            ((D.ι ⊗ₘ D.ι) ≫ mulExtension hD hF) := by
              rw [← id_tensorHom, tensorHom_comp_tensorHom]
        _ = D.ι ⊗ₘ (MonObj.mul (X := D.toFunctor) ≫ D.ι) := by
              rw [hmul, Category.comp_id]
        _ = _ := by rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
    have hassoc := MonoidalCategory.associator_naturality D.ι D.ι D.ι
    calc
      ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) ≫
          ((mulExtension hD hF ▷ F) ≫
            mulExtension hD hF) =
        ((MonObj.mul (X := D.toFunctor) ▷ D.toFunctor) ≫
            MonObj.mul (X := D.toFunctor)) ≫ D.ι := by
              rw [← Category.assoc, hleft]
              simp only [Category.assoc, hmul]
      _ = ((α_ D.toFunctor D.toFunctor D.toFunctor).hom ≫
            (D.toFunctor ◁ MonObj.mul (X := D.toFunctor)) ≫
            MonObj.mul (X := D.toFunctor)) ≫ D.ι := by
              rw [← Category.assoc, MonObj.mul_assoc]
              simp only [Category.assoc]
      _ = (α_ D.toFunctor D.toFunctor D.toFunctor).hom ≫
            (D.toFunctor ◁ MonObj.mul (X := D.toFunctor)) ≫
              ((D.ι ⊗ₘ D.ι) ≫ mulExtension hD hF) := by
                simpa only [Category.assoc] using
                  congrArg (fun θ : D.toFunctor ⊗ D.toFunctor ⟶ F =>
                    (α_ D.toFunctor D.toFunctor D.toFunctor).hom ≫
                      (D.toFunctor ◁ MonObj.mul (X := D.toFunctor)) ≫ θ) hmul.symm
      _ = (α_ D.toFunctor D.toFunctor D.toFunctor).hom ≫
            ((D.ι ⊗ₘ (D.ι ⊗ₘ D.ι)) ≫
              (F ◁ mulExtension hD hF)) ≫ mulExtension hD hF := by
                simpa only [Category.assoc] using
                  congrArg (fun θ : D.toFunctor ⊗
                      (D.toFunctor ⊗ D.toFunctor) ⟶ F ⊗ F =>
                    (α_ D.toFunctor D.toFunctor D.toFunctor).hom ≫ θ ≫
                      mulExtension hD hF) hright.symm
      _ = ((D.ι ⊗ₘ D.ι) ⊗ₘ D.ι) ≫
            ((α_ F F F).hom ≫
              (F ◁ mulExtension hD hF) ≫
              mulExtension hD hF) := by
                simpa only [Category.assoc] using
                  congrArg (fun θ : (D.toFunctor ⊗ D.toFunctor) ⊗
                      D.toFunctor ⟶ F ⊗ (F ⊗ F) =>
                    θ ≫ (F ◁ mulExtension hD hF) ≫ mulExtension hD hF) hassoc.symm
  · apply (oneCoverExtensionEquiv hD hF).injective
    simp only [oneCoverExtensionEquiv_apply]
    have hpair : D.ι ≫ CartesianMonoidalCategory.lift
        (extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι)) (𝟙 F) =
        CartesianMonoidalCategory.lift (GrpObj.inv (X := D.toFunctor))
          (𝟙 D.toFunctor) ≫ (D.ι ⊗ₘ D.ι) := by
      calc
        _ = CartesianMonoidalCategory.lift
            (D.ι ≫ extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι))
            (D.ι ≫ 𝟙 F) := CartesianMonoidalCategory.comp_lift ..
        _ = CartesianMonoidalCategory.lift
            (GrpObj.inv (X := D.toFunctor) ≫ D.ι)
            (𝟙 D.toFunctor ≫ D.ι) := by
              rw [ι_comp_extendOneCover]
              simp
        _ = _ := (CartesianMonoidalCategory.lift_map ..).symm
    calc
      D.ι ≫ (CartesianMonoidalCategory.lift
          (extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι))
          (𝟙 F) ≫ mulExtension hD hF) =
        (CartesianMonoidalCategory.lift (GrpObj.inv (X := D.toFunctor))
            (𝟙 D.toFunctor) ≫ (D.ι ⊗ₘ D.ι)) ≫
            mulExtension hD hF := by rw [← Category.assoc, hpair]
      _ = (CartesianMonoidalCategory.lift (GrpObj.inv (X := D.toFunctor))
            (𝟙 D.toFunctor) ≫ MonObj.mul (X := D.toFunctor)) ≫ D.ι := by
              simp only [Category.assoc, mulExtension_restrict]
      _ = (CartesianMonoidalCategory.toUnit D.toFunctor ≫
          MonObj.one (X := D.toFunctor)) ≫ D.ι := by rw [GrpObj.left_inv]
      _ = D.ι ≫ (CartesianMonoidalCategory.toUnit F ≫
          (MonObj.one (X := D.toFunctor) ≫ D.ι)) := by simp [Category.assoc]
  · apply (oneCoverExtensionEquiv hD hF).injective
    simp only [oneCoverExtensionEquiv_apply]
    have hpair : D.ι ≫ CartesianMonoidalCategory.lift (𝟙 F)
        (extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι)) =
        CartesianMonoidalCategory.lift (𝟙 D.toFunctor)
          (GrpObj.inv (X := D.toFunctor)) ≫ (D.ι ⊗ₘ D.ι) := by
      calc
        _ = CartesianMonoidalCategory.lift (D.ι ≫ 𝟙 F)
            (D.ι ≫ extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι)) :=
              CartesianMonoidalCategory.comp_lift ..
        _ = CartesianMonoidalCategory.lift (𝟙 D.toFunctor ≫ D.ι)
            (GrpObj.inv (X := D.toFunctor) ≫ D.ι) := by
              rw [ι_comp_extendOneCover]
              simp
        _ = _ := (CartesianMonoidalCategory.lift_map ..).symm
    calc
      D.ι ≫ (CartesianMonoidalCategory.lift (𝟙 F)
          (extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι)) ≫
            mulExtension hD hF) =
        (CartesianMonoidalCategory.lift (𝟙 D.toFunctor)
            (GrpObj.inv (X := D.toFunctor)) ≫ (D.ι ⊗ₘ D.ι)) ≫
            mulExtension hD hF := by rw [← Category.assoc, hpair]
      _ = (CartesianMonoidalCategory.lift (𝟙 D.toFunctor)
            (GrpObj.inv (X := D.toFunctor)) ≫ MonObj.mul (X := D.toFunctor)) ≫ D.ι := by
              simp only [Category.assoc, mulExtension_restrict]
      _ = (CartesianMonoidalCategory.toUnit D.toFunctor ≫
          MonObj.one (X := D.toFunctor)) ≫ D.ι := by rw [GrpObj.right_inv]
      _ = D.ι ≫ (CartesianMonoidalCategory.toUnit F ≫
          (MonObj.one (X := D.toFunctor) ≫ D.ι)) := by simp [Category.assoc]

/-- Multiplication of the extension restricts to multiplication on the subfunctor. -/
theorem IsOneCoverDense.grpObj_mul_ι (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    MonObj.mul (X := D.toFunctor) ≫ D.ι =
      (D.ι ⊗ₘ D.ι) ≫ (hD.grpObj hF).toMonObj.mul := by
  exact (mulExtension_restrict hD hF).symm

/-- The unit of the extension restricts to the unit of the subfunctor. -/
theorem IsOneCoverDense.grpObj_one_ι (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    MonObj.one (X := D.toFunctor) ≫ D.ι = (hD.grpObj hF).toMonObj.one := by
  rfl

/-- Inversion of the extension restricts to inversion on the subfunctor. -/
theorem IsOneCoverDense.grpObj_inv_ι (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    GrpObj.inv (X := D.toFunctor) ≫ D.ι = D.ι ≫ (hD.grpObj hF).inv := by
  exact (ι_comp_extendOneCover hD hF (GrpObj.inv (X := D.toFunctor) ≫ D.ι)).symm

/-- The inclusion is a monoid homomorphism for the extended group structure.
Its inverse-preservation equation is `grpObj_inv_ι`. -/
theorem IsOneCoverDense.grpObj_isMonHom (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    @IsMonHom (Cᵒᵖ ⥤ Type w) _ _ D.toFunctor F
      (inferInstance : MonObj D.toFunctor) (hD.grpObj hF).toMonObj D.ι := by
  exact @IsMonHom.mk (Cᵒᵖ ⥤ Type w) _ _ D.toFunctor F
    (inferInstance : MonObj D.toFunctor) (hD.grpObj hF).toMonObj D.ι
      (hD.grpObj_one_ι hF) (hD.grpObj_mul_ι hF)

/-- The extended group law is the only group-object law on the exact ambient
functor for which the inclusion is a monoid homomorphism. -/
theorem IsOneCoverDense.grpObj_unique (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) (other : GrpObj F)
    (hι : @IsMonHom (Cᵒᵖ ⥤ Type w) _ _ D.toFunctor F
      (inferInstance : MonObj D.toFunctor) other.toMonObj D.ι) :
    other = hD.grpObj hF := by
  apply GrpObj.ext
  apply MonObj.ext
  apply tensorRestriction_injective hD hF
  exact hι.mul_hom.symm.trans (hD.grpObj_mul_ι hF)

/-- The multiplication equation on two subfunctor sections. -/
theorem IsOneCoverDense.grpObj_mul_ι_app (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (X : Cᵒᵖ) (a b : D.toFunctor.obj X) :
    ((hD.grpObj hF).toMonObj.mul).app X ((D.ι ⊗ₘ D.ι).app X (a, b)) =
      D.ι.app X ((MonObj.mul (X := D.toFunctor)).app X (a, b)) := by
  calc
    _ = (((D.ι ⊗ₘ D.ι).app X ≫ ((hD.grpObj hF).toMonObj.mul).app X)
        (a, b)) := (types_comp_apply _ _ _).symm
    _ = (((MonObj.mul (X := D.toFunctor)).app X ≫ D.ι.app X) (a, b)) := by
      simpa only [NatTrans.comp_app] using
        congrArg (fun φ => φ.app X (a, b)) (hD.grpObj_mul_ι hF).symm
    _ = _ := types_comp_apply _ _ _

/-- The unit equation at an individual test object. -/
theorem IsOneCoverDense.grpObj_one_ι_app (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (X : Cᵒᵖ) (point : (𝟙_ (Cᵒᵖ ⥤ Type w)).obj X) :
    ((hD.grpObj hF).toMonObj.one).app X point =
      D.ι.app X ((MonObj.one (X := D.toFunctor)).app X point) := by
  simpa only [NatTrans.comp_app, types_comp_apply] using
    congrArg (fun φ => φ.app X point) (hD.grpObj_one_ι hF).symm

/-- Inversion of an included section, evaluated at a test object. -/
theorem IsOneCoverDense.grpObj_inv_ι_app (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (X : Cᵒᵖ) (a : D.toFunctor.obj X) :
    (hD.grpObj hF).inv.app X (D.ι.app X a) =
      D.ι.app X ((GrpObj.inv (X := D.toFunctor)).app X a) := by
  simpa only [NatTrans.comp_app, types_comp_apply] using
    congrArg (fun φ => φ.app X a) (hD.grpObj_inv_ι hF).symm

end CategoryTheory.Subfunctor
