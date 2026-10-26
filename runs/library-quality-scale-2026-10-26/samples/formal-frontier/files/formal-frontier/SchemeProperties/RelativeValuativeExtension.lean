/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import SchemeProperties.NormalValuationStalk
public import SchemeProperties.Integral
public import SchemeProperties.PartialMapGluing
public import SchemeProperties.RationalMapValuativeExtension

/-!
# Relative valuative extension on locally Noetherian schemes

A partial map over a base to a proper target extends across a point whose stalk is a
valuation ring, while retaining its entire original domain. The extension agrees with the
original map as a scheme morphism on that domain, represents the same rational map, and
agrees on the full intersection of the two domains. No reducedness is required away from
the chosen point.

For a normal locally Noetherian source, this applies at every point of coheight at most
one. In particular, the corresponding rational map is defined there in the sense of
`Scheme.RationalMap.domain`. If every point has coheight at most one, the partial map
extends uniquely to a morphism over the base. The dimension-at-most-one specialization
uses `Order.KrullDimLE 1 X`, the absolute dimension of the source.

## Scope

Only the structure morphism of the target is assumed proper; neither the base nor the
target is required to be absolutely separated. There is no integrality, connectedness,
nonemptiness, quasi-compactness or global Noetherianity assumption on the source. The
curve assertion uses arbitrary open covers. Local extension domains are not asserted to
be unique or maximal. The scheme statements allow disconnected sources and generalize
the irreducible-source convention in Milne's §3.

## References

* J. S. Milne, *Abelian Varieties*, version 2.0 (2008), I.3.1: the valuative extension
  argument and its normal-curve consequence.
* Mathlib contributors, especially Andrew Yang's
  `Mathlib.AlgebraicGeometry.Birational.RationalMap`: partial maps, their rational-map
  quotient, relative equality on reduced sources, and the domain of a rational map.
* `SchemeProperties.NormalValuationStalk`: valuation stalks at points of coheight at
  most one. `SchemeProperties.PartialMapGluing`: gluing on the union of an old domain
  and an additional open, without requiring that additional open to be dense.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}}

namespace PartialMap

private theorem inter_hom_eq_of_open_restriction (U : X.Opens) (D : X.Opens)
    (E : U.toScheme.Opens) (f : D.toScheme ⟶ Y) (g : E.toScheme ⟶ Y)
    (h : U.toScheme.homOfLE (inf_le_left : U.ι ⁻¹ᵁ D ⊓ E ≤ U.ι ⁻¹ᵁ D) ≫
        (U.ι ∣_ D) ≫ f =
      U.toScheme.homOfLE (inf_le_right : U.ι ⁻¹ᵁ D ⊓ E ≤ E) ≫ g) :
    X.homOfLE (inf_le_left : D ⊓ U.ι ''ᵁ E ≤ D) ≫ f =
      X.homOfLE (inf_le_right : D ⊓ U.ι ''ᵁ E ≤ U.ι ''ᵁ E) ≫
        (U.ι.isoImage E).inv ≫ g := by
  let T : U.toScheme.Opens := U.ι ⁻¹ᵁ D ⊓ E
  have himage : U.ι ''ᵁ T = D ⊓ U.ι ''ᵁ E := by
    apply TopologicalSpace.Opens.ext
    exact Set.image_preimage_inter U.ι (E : Set U.toScheme) (D : Set X)
  let e : T.toScheme ≅ (D ⊓ U.ι ''ᵁ E).toScheme :=
    U.ι.isoImage T ≪≫ X.isoOfEq himage
  have he : e.hom ≫ (D ⊓ U.ι ''ᵁ E).ι = T.ι ≫ U.ι := by
    simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom,
      Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]
  have hleft : e.hom ≫ X.homOfLE (inf_le_left : D ⊓ U.ι ''ᵁ E ≤ D) =
      U.toScheme.homOfLE (inf_le_left : T ≤ U.ι ⁻¹ᵁ D) ≫ (U.ι ∣_ D) := by
    apply (cancel_mono D.ι).mp
    simpa only [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc,
      morphismRestrict_ι] using he
  have hright : e.hom ≫
      X.homOfLE (inf_le_right : D ⊓ U.ι ''ᵁ E ≤ U.ι ''ᵁ E) ≫
        (U.ι.isoImage E).inv =
      U.toScheme.homOfLE (inf_le_right : T ≤ E) := by
    apply (cancel_mono (E.ι ≫ U.ι)).mp
    simpa only [Category.assoc, Scheme.Hom.isoImage_inv_ι,
      Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc] using he
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (X.homOfLE (inf_le_left : D ⊓ U.ι ''ᵁ E ≤ D) ≫ f) =
        (U.toScheme.homOfLE (inf_le_left : T ≤ U.ι ⁻¹ᵁ D) ≫ (U.ι ∣_ D)) ≫ f := by
      rw [← Category.assoc, hleft]
    _ = U.toScheme.homOfLE (inf_le_right : T ≤ E) ≫ g := by
      simpa only [Category.assoc] using h
    _ = e.hom ≫
        (X.homOfLE (inf_le_right : D ⊓ U.ι ''ᵁ E ≤ U.ι ''ᵁ E) ≫
          (U.ι.isoImage E).inv ≫ g) := by
      rw [← hright]
      simp only [Category.assoc]

/-- Relative valuative extension at a valuation stalk, retaining the whole old domain.

The new partial map contains the chosen point and the old domain, is over the same base,
and restricts to the original scheme morphism on its entire domain. It represents the
same rational map and agrees with the original morphism on the full intersection.

This is the relative scheme form of the valuative argument in Milne, *Abelian Varieties*,
I.3.1, applied on an integral neighborhood of the point. The source need not be reduced
on its other components. The domain dictionary is explicit because `ValuationRing` takes
an `IsDomain` instance as a parameter. -/
theorem exists_le_extension_of_valuationRing_stalk
    [IsLocallyNoetherian X] (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (p : X.PartialMap Y) (hp : p.hom ≫ sY = p.domain.ι ≫ sX) (x : X)
    [_root_.IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)] :
    ∃ q : X.PartialMap Y, x ∈ q.domain ∧
      ∃ hD : p.domain ≤ q.domain,
        q.hom ≫ sY = q.domain.ι ≫ sX ∧
        X.homOfLE hD ≫ q.hom = p.hom ∧
        q.toRationalMap = p.toRationalMap ∧
        X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
          X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  classical
  obtain ⟨U, hxU, hU⟩ := exists_isIntegral_open_of_isDomain_stalk X x
  letI : IsIntegral U.toScheme := hU
  let xU : U.toScheme := ⟨x, hxU⟩
  letI : _root_.IsDomain (U.toScheme.presheaf.stalk xU) :=
    (U.stalkIso xU).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
      (X.presheaf.stalk x)
  letI : ValuationRing (U.toScheme.presheaf.stalk xU) :=
    Function.Surjective.valuationRing
      (U.stalkIso xU).symm.commRingCatIsoToRingEquiv.toRingHom
      (U.stalkIso xU).symm.commRingCatIsoToRingEquiv.surjective
  let pU : U.toScheme.PartialMap Y :=
    { domain := U.ι ⁻¹ᵁ p.domain
      dense_domain := p.dense_domain.preimage U.ι.isOpenEmbedding.isOpenMap
      hom := (U.ι ∣_ p.domain) ≫ p.hom }
  have hpU : pU.hom ≫ sY = pU.domain.ι ≫ (U.ι ≫ sX) := by
    change ((U.ι ∣_ p.domain) ≫ p.hom) ≫ sY =
      (U.ι ⁻¹ᵁ p.domain).ι ≫ (U.ι ≫ sX)
    rw [Category.assoc, hp, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  obtain ⟨qU, hxqU, hqUS, _, hinter⟩ :=
    exists_extension_of_valuationRing_stalk (U.ι ≫ sX) sY pU hpU xU
  -- The open image need not be dense in the whole source.
  let V : X.Opens := U.ι ''ᵁ qU.domain
  let b : V.toScheme ⟶ Y := (U.ι.isoImage qU.domain).inv ≫ qU.hom
  have hxV : x ∈ V := ⟨xU, hxqU, rfl⟩
  have hb : b ≫ sY = V.ι ≫ sX := by
    dsimp only [b]
    rw [Category.assoc, hqUS]
    exact Scheme.Hom.isoImage_inv_ι_assoc U.ι qU.domain sX
  have hcompat : X.homOfLE (inf_le_left : p.domain ⊓ V ≤ p.domain) ≫ p.hom =
      X.homOfLE (inf_le_right : p.domain ⊓ V ≤ V) ≫ b :=
    inter_hom_eq_of_open_restriction U p.domain qU.domain p.hom qU.hom hinter
  let q : X.PartialMap Y := p.glueHom V b hcompat
  have hD : p.domain ≤ q.domain := le_sup_left
  have hread : X.homOfLE hD ≫ q.hom = p.hom :=
    homOfLE_glueHom_left p V b hcompat
  letI : X.Over S := .ofHom sX
  letI : Y.Over S := .ofHom sY
  letI : p.IsOver S := (isOver_iff (S := S) (f := p)).mpr hp
  letI : b.IsOver S := (Scheme.Hom.isOver_iff (S := S) (f := b)).mpr hb
  have hqS : q.hom ≫ sY = q.domain.ι ≫ sX :=
    (isOver_iff (S := S) (f := q)).mp (inferInstance : q.IsOver S)
  refine ⟨q, (show x ∈ p.domain ⊔ V from Or.inr hxV), hD, hqS, hread,
    glueHom_toRationalMap p V b hcompat, ?_⟩
  calc
    X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
        X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫
          (X.homOfLE hD ≫ q.hom) := by rw [hread]
    _ = X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
      rw [← Category.assoc, Scheme.homOfLE_homOfLE]

/-- Relative extension across a point of coheight at most one on a normal locally
Noetherian scheme, retaining the whole original domain and its scheme morphism.

This generalizes the codimension-one extension in Milne, *Abelian Varieties*, I.3.1,
to possibly disconnected normal schemes over an arbitrary base. Coheight zero is
included; the stalk is not required to be a discrete valuation ring. -/
theorem exists_le_extension_of_coheight_le_one [IsNormal X] [IsLocallyNoetherian X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (p : X.PartialMap Y) (hp : p.hom ≫ sY = p.domain.ι ≫ sX)
    (x : X) (hx : Order.coheight x ≤ 1) :
    ∃ q : X.PartialMap Y, x ∈ q.domain ∧
      ∃ hD : p.domain ≤ q.domain,
        q.hom ≫ sY = q.domain.ι ≫ sX ∧
        X.homOfLE hD ≫ q.hom = p.hom ∧
        q.toRationalMap = p.toRationalMap ∧
        X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
          X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  letI : ValuationRing (X.presheaf.stalk x) :=
    valuationRing_stalk_of_coheight_le_one x hx
  exact exists_le_extension_of_valuationRing_stalk sX sY p hp x

/-- A partial map over a base to a proper target represents a rational map defined
at every point of coheight at most one of a normal locally Noetherian source.

Definedness here is membership in `RationalMap.domain`, as characterized by
`RationalMap.mem_domain`; no absolutely separated target is assumed. -/
theorem mem_domain_toRationalMap_of_coheight_le_one [IsNormal X] [IsLocallyNoetherian X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (p : X.PartialMap Y) (hp : p.hom ≫ sY = p.domain.ι ≫ sX)
    (x : X) (hx : Order.coheight x ≤ 1) :
    x ∈ p.toRationalMap.domain := by
  obtain ⟨q, hxq, _, _, _, hq, _⟩ :=
    exists_le_extension_of_coheight_le_one sX sY p hp x hx
  exact RationalMap.mem_domain.mpr ⟨q, hxq, hq⟩

/-- A relative partial map from a normal locally Noetherian scheme of absolute
dimension at most one to a proper target extends uniquely over the base.

The extension restricts to the given scheme morphism on its whole original domain.
This is the arbitrary-base normal-curve consequence of Milne, *Abelian Varieties*,
I.3.1, allowing disconnected sources. The open cover used for extension need not be
finite; the source may be empty or non-quasi-compact. `Order.KrullDimLE 1 X` bounds
the absolute dimension of the source, not the relative dimension over the base. -/
theorem existsUnique_extension_of_krullDimLE_one [IsNormal X] [IsLocallyNoetherian X]
    [Order.KrullDimLE 1 X] (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (p : X.PartialMap Y) (hp : p.hom ≫ sY = p.domain.ι ≫ sX) :
    ∃! h : X ⟶ Y, h ≫ sY = sX ∧ p.domain.ι ≫ h = p.hom := by
  classical
  have hx (x : X) : Order.coheight x ≤ 1 := by
    exact WithBot.coe_le_coe.mp <|
      (Order.coheight_le_krullDim x).trans
        (Order.KrullDimLE.krullDim_le (n := 1) (α := X))
  have hlocal (x : X) : ∃ q : X.PartialMap Y, x ∈ q.domain ∧
      q.hom ≫ sY = q.domain.ι ≫ sX ∧ q.toRationalMap = p.toRationalMap := by
    obtain ⟨q, hxq, _, hqS, _, hqrat, _⟩ :=
      exists_le_extension_of_coheight_le_one sX sY p hp x (hx x)
    exact ⟨q, hxq, hqS, hqrat⟩
  choose q hxq hqS hqrat using hlocal
  -- Include the old domain as a cover member, even when the source is empty.
  let r : Option X → X.PartialMap Y := fun i ↦ i.elim p q
  have hrS (i : Option X) : (r i).hom ≫ sY = (r i).domain.ι ≫ sX := by
    cases i with
    | none => exact hp
    | some x => exact hqS x
  have hrat (i : Option X) : (r i).toRationalMap = p.toRationalMap := by
    cases i with
    | none => rfl
    | some x => exact hqrat x
  let C : X.OpenCover := Cover.mkOfCovers (Option X)
    (fun i ↦ (r i).domain.toScheme) (fun i ↦ (r i).domain.ι)
    (fun x ↦ ⟨some x, ⟨x, hxq x⟩, rfl⟩)
    (fun _ ↦ inferInstance)
  let k : ∀ i : C.I₀, C.X i ⟶ Y := fun i ↦ (r i).hom
  let : X.Over S := .ofHom sX
  let : Y.Over S := .ofHom sY
  let : IsSeparated (Y ↘ S) := (inferInstance : IsSeparated sY)
  have hcompat : ∀ i j, CategoryTheory.Limits.pullback.fst (C.f i) (C.f j) ≫ k i =
      CategoryTheory.Limits.pullback.snd (C.f i) (C.f j) ≫ k j := by
    change ∀ i j : Option X,
      CategoryTheory.Limits.pullback.fst (r i).domain.ι (r j).domain.ι ≫ (r i).hom =
        CategoryTheory.Limits.pullback.snd (r i).domain.ι (r j).domain.ι ≫ (r j).hom
    intro i j
    let : (r i).IsOver S := (isOver_iff (S := S) (f := r i)).mpr (hrS i)
    let : (r j).IsOver S := (isOver_iff (S := S) (f := r j)).mpr (hrS j)
    have hequiv : (r i).equiv (r j) :=
      toRationalMap_eq_iff.mp ((hrat i).trans (hrat j).symm)
    have hfull := (equiv_iff_of_isSeparated (S := S) (f := r i) (g := r j)).mp hequiv
    dsimp only [restrict] at hfull
    refine (cancel_epi
      (isPullback_opens_inf (r i).domain (r j).domain).isoPullback.hom).mp ?_
    simpa only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc] using hfull
  let h : X ⟶ Y := C.glueMorphisms k hcompat
  have hread (i : Option X) : (r i).domain.ι ≫ h = (r i).hom :=
    C.ι_glueMorphisms k hcompat i
  have hS : h ≫ sY = sX := by
    apply C.hom_ext
    intro i
    change (r i).domain.ι ≫ (h ≫ sY) = (r i).domain.ι ≫ sX
    rw [← Category.assoc, hread i, hrS i]
  refine ⟨h, ⟨hS, hread none⟩, ?_⟩
  intro g hg
  letI : IsDominant p.domain.ι := Opens.isDominant_ι p.dense_domain
  exact ext_of_isDominant_of_isSeparated sY (hg.1.trans hS.symm) p.domain.ι
    (hg.2.trans (hread none).symm)

end PartialMap

namespace RationalMap

/-- An over-base rational map to a proper target is defined at every point of
coheight at most one of a normal locally Noetherian source.

The over-base hypothesis supplies an over-base partial representative through
`exists_partialMap_over`. Definedness is membership in `RationalMap.domain`, not a
choice of a maximal partial representative or a claim that every representative is
over the base. This is the relative form of Milne, *Abelian Varieties*, I.3.1. -/
theorem mem_domain_of_coheight_le_one [IsNormal X] [IsLocallyNoetherian X]
    [X.Over S] [Y.Over S] [IsProper (Y ↘ S)] (f : X ⤏ Y) [f.IsOver S]
    (x : X) (hx : Order.coheight x ≤ 1) : x ∈ f.domain := by
  obtain ⟨p, hp, rfl⟩ := f.exists_partialMap_over S
  exact PartialMap.mem_domain_toRationalMap_of_coheight_le_one (X ↘ S) (Y ↘ S) p
    ((PartialMap.isOver_iff (S := S) (f := p)).mp hp) x hx

end RationalMap

end AlgebraicGeometry.Scheme
