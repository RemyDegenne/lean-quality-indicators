/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
The Mathlib notice above applies to the adapted dense smooth-locus proof.
Modifications by Formal Frontier Agents: adapt Mathlib's
`Scheme.Hom.dense_smoothLocus_of_perfectField` to geometrically reduced schemes.
-/
module

public import AlgebraicGroups.FieldTheory.GeometricallyReduced
public import AlgebraicGroups.Scheme.JointlySchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Smooth loci of geometrically reduced schemes

This file connects scheme-theoretic geometric reducedness with the corresponding algebraic
predicate on affine opens. It then proves generic smoothness, and density of the smooth locus, for
a geometrically reduced scheme locally of finite presentation over an arbitrary field.

## Main results

- `AlgebraicGeometry.Algebra.isGeometricallyReduced_of_geometricallyReduced_appLE`
- `AlgebraicGeometry.GeometricallyReduced.comp_of_flat_of_locallyOfFiniteType`
- `AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_geometricallyReduced`
- `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_geometricallyReduced`
- `AlgebraicGeometry.RationalPointSet.dense_underlyingPoints_of_smooth`
- `AlgebraicGeometry.RationalPointSet.dense_underlyingPoints_of_isSepClosed`
- `AlgebraicGeometry.FieldValuedPoints.schematicallyDense_of_geometricallyReduced_of_isSepClosed`
- `AlgebraicGeometry.FieldValuedPoints.eq_of_subschemePoints_eq_of_isSepClosed`

## References

- J. S. Milne, *Algebraic Groups*, Appendix A.48 and Corollaries 1.17--1.18,
  for density of separably closed points and determination of geometrically
  reduced closed subvarieties from those points.
- The Stacks Project, [Lemma 33.25.7 (Tag 056V)](https://stacks.math.columbia.edu/tag/056V),
  for the dense smooth locus of a geometrically reduced scheme locally of finite type
  over a field, and [Lemma 10.44.2 (Tag 030W)](https://stacks.math.columbia.edu/tag/030W)
  for the field-extension separability criterion used at generic points.
- Mathlib's `Scheme.Hom.dense_smoothLocus_of_perfectField` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` supplies the adapted dense-locus proof:
  the generic-point step here uses geometric reducedness in place of a perfect base field.
- Mathlib's `GeometricallyReduced.geometrically_isReduced`,
  `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`,
  `Scheme.Hom.smoothLocus`, and `Scheme.exists_fac_of_etale_of_isSepClosed`
  provide the relative geometric-reducedness, smooth-locus, and étale-point APIs.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Geometric reducedness of scheme morphisms respects isomorphisms. -/
instance : MorphismProperty.RespectsIso @GeometricallyReduced :=
  GeometricallyReduced.eq_geometrically ▸ inferInstance

/-- Restricting the source of a geometrically reduced morphism to an open subscheme preserves
geometric reducedness. -/
lemma GeometricallyReduced.comp_of_isOpenImmersion {U X S : Scheme.{u}}
    (j : U ⟶ X) (f : X ⟶ S) [IsOpenImmersion j]
    [GeometricallyReduced f] : GeometricallyReduced (j ≫ f) := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K _ y Z fst snd h
  let e : Z ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc, h.w])
  have he : IsPullback fst e j (pullback.fst f y) := by
    apply ((IsPullback.of_hasPullback f y).paste_vert_iff (by
      simp only [e, pullback.lift_fst])).mp
    convert h using 1 ; simp only [e, pullback.lift_snd]
  have _ : IsOpenImmersion e := MorphismProperty.of_isPullback he inferInstance
  have _ : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced y _ _ (IsPullback.of_hasPullback f y)
  exact isReduced_of_isOpenImmersion e

/-- A composite of geometrically reduced morphisms is geometrically reduced if the first
morphism is flat and the second is locally of finite type. -/
lemma GeometricallyReduced.comp_of_flat_of_locallyOfFiniteType
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyReduced f] [Flat f]
    [GeometricallyReduced g] [LocallyOfFiniteType g] :
    GeometricallyReduced (f ≫ g) := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K _ z W fst snd h
  let hb : IsPullback (pullback.fst g z) (pullback.snd g z) g z :=
    IsPullback.of_hasPullback g z
  let q : W ⟶ pullback g z :=
    hb.lift (fst ≫ f) snd (by rw [Category.assoc, h.w])
  have hq : IsPullback fst q f (pullback.fst g z) := by
    dsimp only [q]
    exact IsPullback.of_bot' h hb
  let _ : GeometricallyReduced q :=
    MorphismProperty.of_isPullback hq inferInstance
  let _ : Flat q := MorphismProperty.of_isPullback hq inferInstance
  let _ : IsReduced (pullback g z) :=
    GeometricallyReduced.geometrically_isReduced z _ _
      (IsPullback.of_hasPullback g z)
  let _ : IsLocallyNoetherian (pullback g z) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g z)
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian q

/-- If a composite with a monomorphism is geometrically reduced, so is its first factor. -/
lemma GeometricallyReduced.of_comp_mono {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] [GeometricallyReduced (f ≫ g)] :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K _ y P fst snd h
  have hout : IsPullback fst snd (f ≫ g) (y ≫ g) := {
    w := by rw [← Category.assoc, ← Category.assoc, h.w]
    isLimit' := ⟨PullbackCone.isLimitOfCompMono f y g h.cone h.isLimit⟩ }
  exact (inferInstance : GeometricallyReduced (f ≫ g)).geometrically_isReduced
    (y ≫ g) fst snd hout

/-- Scheme-theoretic geometric reducedness of an affine morphism over a field implies algebraic
geometric reducedness of its coordinate algebra. -/
lemma Algebra.isGeometricallyReduced_of_geometricallyReduced_spec
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let E := AlgebraicClosure k
  let f : Spec (.of A) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  let y : Spec (.of E) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k E))
  have _ : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced y _ _ (IsPullback.of_hasPullback f y)
  let e : pullback f y ≅ Spec (.of (E ⊗[k] A)) :=
    pullbackSymmetry f y ≪≫ pullbackSpecIso k E A
  have _ : IsReduced (Spec (.of (E ⊗[k] A))) := isReduced_of_isOpenImmersion e.inv
  exact (affine_isReduced_iff (.of (E ⊗[k] A))).mp inferInstance

/-- Geometric reducedness of an affine scheme morphism over a field implies geometric reducedness
of the induced map on global sections. -/
lemma Algebra.isGeometricallyReduced_of_geometricallyReduced_appTop
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [GeometricallyReduced f] (hY : IsField Γ(Y, ⊤)) :
    letI := (f.appTop).hom.toAlgebra
    Algebra.IsGeometricallyReduced Γ(Y, ⊤) Γ(X, ⊤) := by
  let _ := hY.toField
  algebraize [(f.appTop).hom]
  have hspec : GeometricallyReduced (Spec.map f.appTop) := by
    rw [← MorphismProperty.arrow_mk_iso_iff @GeometricallyReduced
      (arrowIsoSpecΓOfIsAffine f)]
    infer_instance
  let _ : GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))) := by
    change GeometricallyReduced (Spec.map f.appTop)
    exact hspec
  exact Algebra.isGeometricallyReduced_of_geometricallyReduced_spec _ _

private noncomputable def arrowResLESpecIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) :
    Arrow.mk (f.resLE U V e) ≅ Arrow.mk (Spec.map (f.appLE U V e)) := by
  refine Arrow.isoMk hV.isoSpec hU.isoSpec ?_
  apply (cancel_mono (hU.isoSpec.inv ≫ U.ι)).1
  simp only [Arrow.mk_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (Spec.map (f.appLE U V e)) hU.isoSpec.inv U.ι]
  change hV.isoSpec.hom ≫ Spec.map (f.appLE U V e) ≫ hU.fromSpec =
    f.resLE U V e ≫ U.ι
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
  rw [← Category.assoc, hV.isoSpec_hom_fromSpec, Scheme.Hom.resLE_comp_ι]

/-- Geometric reducedness of a scheme morphism over a field implies geometric reducedness of the
map on sections over compatible affine opens. -/
lemma Algebra.isGeometricallyReduced_of_geometricallyReduced_appLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    [GeometricallyReduced f] (hField : IsField Γ(Y, U)) :
    letI := (f.appLE U V e).hom.toAlgebra
    Algebra.IsGeometricallyReduced Γ(Y, U) Γ(X, V) := by
  let _ := hField.toField
  algebraize [(f.appLE U V e).hom]
  have hcomp : GeometricallyReduced (f.resLE U V e ≫ U.ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    exact GeometricallyReduced.comp_of_isOpenImmersion V.ι f
  let _ : GeometricallyReduced (f.resLE U V e ≫ U.ι) := hcomp
  let _ : GeometricallyReduced (f.resLE U V e) :=
    GeometricallyReduced.of_comp_mono _ U.ι
  have hspec : GeometricallyReduced (Spec.map (f.appLE U V e)) := by
    rw [← MorphismProperty.arrow_mk_iso_iff @GeometricallyReduced
      (arrowResLESpecIso f U hU V hV e)]
    infer_instance
  let _ : GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, V)))) := by
    change GeometricallyReduced (Spec.map (f.appLE U V e))
    exact hspec
  exact Algebra.isGeometricallyReduced_of_geometricallyReduced_spec _ _

set_option backward.isDefEq.respectTransparency false in
/-- The generic point of an integral geometrically reduced scheme locally of finite presentation
over a field belongs to its smooth locus; compare the generic-point step of the Stacks Project,
Lemma 33.25.7 (Tag 056V). -/
lemma Scheme.Hom.genericPoint_mem_smoothLocus_of_geometricallyReduced
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    [GeometricallyReduced f] : genericPoint X ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hgeneric, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint X)) isOpen_univ
  let U : (Spec (.of K)).Opens := ⊤
  have hU : IsAffineOpen U := by simpa [U] using isAffineOpen_top (Spec (.of K))
  have hVU : V ≤ f ⁻¹ᵁ U := by simp [U]
  let hK : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  rw [Scheme.Hom.mem_smoothLocus,
    formallySmooth_stalkMap_iff U hU V hV hVU hgeneric]
  let _ := hK.toField
  algebraize [(f.appLE U V hVU).hom]
  have _ : Algebra.FinitePresentation Γ(Spec (.of K), U) Γ(X, V) :=
    f.finitePresentation_appLE hU hV hVU
  have _ : Algebra.IsGeometricallyReduced Γ(Spec (.of K), U) Γ(X, V) :=
    Algebra.isGeometricallyReduced_of_geometricallyReduced_appLE f U hU V hV hVU
      (by simpa [U] using hK)
  let _ : Nonempty V := ⟨⟨genericPoint X, hgeneric⟩⟩
  rw [IsAffineOpen.primeIdealOf_genericPoint
    (show IsAffineOpen V from hV), genericPoint_eq_bot_of_affine]
  let _ : IsFractionRing Γ(X, V)
      (Localization.AtPrime (⊥ : Ideal Γ(X, V))) := by
    change IsLocalization (nonZeroDivisors Γ(X, V))
      (Localization.AtPrime (⊥ : Ideal Γ(X, V)))
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let _ : Field (Localization.AtPrime (⊥ : Ideal Γ(X, V))) :=
    IsFractionRing.toField Γ(X, V)
  have _ : Algebra.IsGeometricallyReduced Γ(Spec (.of K), U)
      (Localization.AtPrime (⊥ : Ideal Γ(X, V))) :=
    Algebra.IsGeometricallyReduced.of_isLocalization
      ((⊥ : Ideal Γ(X, V)).primeCompl)
  change Algebra.FormallySmooth Γ(Spec (.of K), U)
    (Localization.AtPrime (⊥ : Ideal Γ(X, V)))
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- A geometrically reduced scheme locally of finite presentation over a field has dense smooth
locus. The proof adapts Mathlib's `Scheme.Hom.dense_smoothLocus_of_perfectField`, replacing
perfectness of the base field with geometric reducedness of the morphism. See the Stacks Project,
Lemma 33.25.7 (Tag 056V). -/
lemma Scheme.Hom.dense_smoothLocus_of_geometricallyReduced
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    [GeometricallyReduced f] : Dense (f.smoothLocus : Set X) := by
  let _ : Flat f := by infer_instance
  let _ : IsReduced X :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  wlog H : CompactSpace X generalizing X
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let _ : GeometricallyReduced (U.ι ≫ f) :=
      GeometricallyReduced.comp_of_isOpenImmersion U.ι f
    have := this (U.ι ≫ f) (isCompact_iff_compactSpace.mp hU.isCompact) ⟨x, hxU⟩
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.coe_preimage,
      ← U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.ι.continuous,
      Set.mem_preimage, U.ι_apply] at this
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  let U : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hU : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents x)
  have : AlgebraicGeometry.IsIntegral U :=
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hU ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hsmooth : U.ι (genericPoint U) ∈ f.smoothLocus := by
    let _ : GeometricallyReduced (U.ι ≫ f) :=
      GeometricallyReduced.comp_of_isOpenImmersion U.ι f
    have := (U.ι ≫ f).genericPoint_mem_smoothLocus_of_geometricallyReduced
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at this
  exact (((genericPoint_spec U).image U.ι.continuous).specializes (y := x)
    (by rw [Set.image_univ, U.range_ι, hU]; exact mem_irreducibleComponent)).mem_closed
    isClosed_closure (subset_closure hsmooth)

private lemma exists_specMap_eval₂_mem
    {R K : Type u} [CommRing R] [Field K] [Infinite K] {σ : Type}
    (ι : R →+* K) (hι : Function.Injective ι)
    (U : Set (Spec (.of (MvPolynomial σ R)))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a : σ → K,
      (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ι a)) : Spec (.of K) ⟶ _) default ∈ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨w, hw, hxw, hwU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx hU
  rcases hw with ⟨gopen, ⟨g, rfl⟩, rfl⟩
  dsimp only at hxw hwU
  have hg : g ≠ 0 := by
    intro h
    subst g
    change (0 : MvPolynomial σ R) ∉ x.asIdeal at hxw
    exact hxw (Ideal.zero_mem x.asIdeal)
  have hmap : MvPolynomial.map ι g ≠ 0 := fun h ↦ hg <| by
    apply MvPolynomial.map_injective ι hι
    simpa using h
  have : ∃ a : σ → K, MvPolynomial.eval a (MvPolynomial.map ι g) ≠ 0 := by
    by_contra H
    simp only [not_exists, ne_eq, not_not] at H
    exact hmap (MvPolynomial.funext fun a ↦ by simpa using H a)
  obtain ⟨a, ha⟩ := this
  refine ⟨a, hwU ?_⟩
  change PrimeSpectrum.comap (MvPolynomial.eval₂Hom ι a) (⊥ : PrimeSpectrum K) ∈
    PrimeSpectrum.basicOpen g
  rw [PrimeSpectrum.mem_basicOpen]
  change MvPolynomial.eval₂Hom ι a g ∉ (⊥ : Ideal K)
  simpa using ha

private lemma exists_point_mem_open_of_isStandardSmooth
    {R K A : Type u} [CommRing R] [Field K] [IsSepClosed K] [CommRing A]
    (ι : R →+* K) (hι : Function.Injective ι)
    (f : R →+* A) (hf : f.IsStandardSmooth)
    (U : Set (Spec (.of A))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ l : Spec (.of K) ⟶ Spec (.of A),
      l ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom ι) ∧
        l default ∈ U := by
  obtain ⟨n, g, hgf, hg⟩ := hf.exists_etale_mvPolynomial
  let e : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin n) R)) :=
    Spec.map (CommRingCat.ofHom g)
  have _ : Etale e := HasRingHomProperty.Spec_iff.mpr hg
  have heU : IsOpen (e '' U) := e.isOpenMap U hU
  have hene : (e '' U).Nonempty := hne.image e
  obtain ⟨a, ha⟩ := exists_specMap_eval₂_mem (K := K) (σ := Fin n) ι hι
    (e '' U) heU hene
  let s : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Fin n) R)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ι a))
  obtain ⟨x, hxU, hxe⟩ := ha
  change e x = s default at hxe
  obtain ⟨l, hle, hlx⟩ := Scheme.exists_fac_of_etale_of_isSepClosed e s x hxe
  refine ⟨l, ?_, hlx ▸ hxU⟩
  rw [← hgf, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, hle]
  dsimp [s]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext r
  simp

namespace RationalPointSet

set_option backward.isDefEq.respectTransparency false in
/-- The rational points of a smooth scheme over a separably closed field are dense; this is
the smooth case of the density used in Milne, *Algebraic Groups*, Appendix A.48.
The proof uses Mathlib's lifting of étale points and evaluation of polynomials. -/
theorem dense_underlyingPoints_of_smooth
    {K : Type u} [Field K] [IsSepClosed K]
    {Y : Over (Spec (.of K))} [Smooth Y.hom] :
    Dense (underlyingPoints (Set.univ : Set (RationalPoint Y))) := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨x, hxO⟩ := hOne
  obtain ⟨U, hU, V, hV, hxV, e, he⟩ := Smooth.exists_isStandardSmooth Y.hom x
  have hUtop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    rw [Subsingleton.elim y (Y.hom x)]
    exact e hxV
  subst U
  let kEquiv : Γ(Spec (.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  let W : Set (Spec (.of Γ(Y.left, V))) := hV.fromSpec ⁻¹' O
  have hWopen : IsOpen W := hO.preimage hV.fromSpec.continuous
  have hz : hV.fromSpec (hV.isoSpec.hom ⟨x, hxV⟩) = x := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom_fromSpec,
      Scheme.Opens.ι_apply]
  have hWne : W.Nonempty := by
    refine ⟨hV.isoSpec.hom ⟨x, hxV⟩, ?_⟩
    change hV.fromSpec (hV.isoSpec.hom ⟨x, hxV⟩) ∈ O
    rwa [hz]
  obtain ⟨l, hlbase, hlW⟩ := exists_point_mem_open_of_isStandardSmooth
    kEquiv.toRingHom kEquiv.injective (Y.hom.appLE (⊤ : (Spec (.of K)).Opens) V e).hom
      he W hWopen hWne
  change l ≫ Spec.map (Y.hom.appLE (⊤ : (Spec (.of K)).Opens) V e) =
    Spec.map (Scheme.ΓSpecIso (.of K)).hom at hlbase
  let pHom : Spec (.of K) ⟶ Y.left := l ≫ hV.fromSpec
  have hpbase : pHom ≫ Y.hom = 𝟙 _ := by
    dsimp [pHom]
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom
      (isAffineOpen_top (Spec (.of K))) hV e, ← Category.assoc l, hlbase]
    rw [← Scheme.isoSpec_Spec_hom]
    rw [IsAffineOpen.fromSpec_top, Iso.hom_inv_id]
  let p : RationalPoint Y := ⟨pHom, hpbase⟩
  refine ⟨pHom default, ?_, ?_⟩
  · exact hlW
  · rw [mem_underlyingPoints]
    exact ⟨⟨p, Set.mem_univ p⟩, default, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The rational points of a geometrically reduced scheme locally of finite type over a
separably closed field are dense, as in Milne, *Algebraic Groups*, Appendix A.48.
Here the argument passes through the dense smooth locus rather than its
birational-hypersurface presentation. -/
theorem dense_underlyingPoints_of_isSepClosed
    {K : Type u} [Field K] [IsSepClosed K]
    {Y : Over (Spec (.of K))} [LocallyOfFiniteType Y.hom]
    [GeometricallyReduced Y.hom] :
    Dense (underlyingPoints (Set.univ : Set (RationalPoint Y))) := by
  let S : Y.left.Opens := Y.hom.smoothLocus
  let Y' : Over (Spec (.of K)) := Over.mk (S.ι ≫ Y.hom)
  have hlft : LocallyOfFiniteType Y'.hom := by
    dsimp [Y']
    infer_instance
  let _ : LocallyOfFiniteType Y'.hom := hlft
  have hlfp : LocallyOfFinitePresentation Y'.hom := by infer_instance
  let _ : LocallyOfFinitePresentation Y'.hom := hlfp
  have hsmooth : Smooth Y'.hom := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    change (S.ι ≫ Y.hom).smoothLocus = ⊤
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    ext x
    simp [S]
  let _ : Smooth Y'.hom := hsmooth
  have hdenseS : Dense (S : Set Y.left) :=
    Y.hom.dense_smoothLocus_of_geometricallyReduced
  have hdenseRat : Dense
      (underlyingPoints (Set.univ : Set (RationalPoint Y'))) :=
    dense_underlyingPoints_of_smooth
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨x, hxS, hxO⟩ := hdenseS.exists_mem_open hO hOne
  let W : Set Y'.left := S.ι ⁻¹' O
  have hWopen : IsOpen W := hO.preimage S.ι.continuous
  have hWne : W.Nonempty := ⟨⟨x, hxS⟩, hxO⟩
  obtain ⟨z, hzRat, hzW⟩ := hdenseRat.exists_mem_open hWopen hWne
  rw [mem_underlyingPoints] at hzRat
  obtain ⟨q, t, rfl⟩ := hzRat
  let pHom : Spec (.of K) ⟶ Y.left := q.1.1 ≫ S.ι
  have hpbase : pHom ≫ Y.hom = 𝟙 _ := by
    simpa [pHom, Y', ← Category.assoc] using q.1.2
  let p : RationalPoint Y := ⟨pHom, hpbase⟩
  refine ⟨pHom t, ?_, ?_⟩
  · exact hzW
  · rw [mem_underlyingPoints]
    exact ⟨⟨p, Set.mem_univ p⟩, t, rfl⟩

end RationalPointSet

namespace FieldValuedPoints

/-- All points valued in a separably closed extension are schematically dense in a geometrically
reduced scheme locally of finite type over a field. This is Milne, *Algebraic Groups*,
Corollary 1.17, using rational-point density and Proposition 1.16. -/
theorem schematicallyDense_of_geometricallyReduced_of_isSepClosed
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsSepClosed L]
    {Y : Over (Spec (.of K))} [LocallyOfFiniteType Y.hom]
    [GeometricallyReduced Y.hom] :
    SchematicallyDense (Y := Y) (L := L) := by
  let _ : LocallyOfFiniteType (baseChange (L := L) Y).hom := by
    dsimp [baseChange]
    infer_instance
  let _ : GeometricallyReduced (baseChange (L := L) Y).hom := by
    dsimp [baseChange]
    infer_instance
  apply schematicallyDense_of_geometricallyReduced_of_dense_baseChange
  exact RationalPointSet.dense_underlyingPoints_of_isSepClosed

/-- Geometrically reduced closed subschemes locally of finite type over a field are determined by
their points in a separably closed extension. This is the closed-subvariety assertion of Milne,
*Algebraic Groups*, Corollary 1.18, without requiring a finite-type ambient scheme. -/
theorem eq_of_subschemePoints_eq_of_isSepClosed
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsSepClosed L]
    {Y : Over (Spec (.of K))} (I J : Y.left.IdealSheafData)
    [LocallyOfFiniteType (I.subschemeι ≫ Y.hom)]
    [GeometricallyReduced (I.subschemeι ≫ Y.hom)]
    [LocallyOfFiniteType (J.subschemeι ≫ Y.hom)]
    [GeometricallyReduced (J.subschemeι ≫ Y.hom)]
    (h : subschemePoints (L := L) I = subschemePoints (L := L) J) :
    I = J := by
  let _ : LocallyOfFiniteType (Over.mk (I.subschemeι ≫ Y.hom)).hom := by
    dsimp
    infer_instance
  let _ : GeometricallyReduced (Over.mk (I.subschemeι ≫ Y.hom)).hom := by
    dsimp
    infer_instance
  let _ : LocallyOfFiniteType (Over.mk (J.subschemeι ≫ Y.hom)).hom := by
    dsimp
    infer_instance
  let _ : GeometricallyReduced (Over.mk (J.subschemeι ≫ Y.hom)).hom := by
    dsimp
    infer_instance
  apply eq_of_schematicallyDense_of_subschemePoints_eq
    (K := K) (L := L) (Y := Y) I J
  · exact schematicallyDense_of_geometricallyReduced_of_isSepClosed
  · exact schematicallyDense_of_geometricallyReduced_of_isSepClosed
  · exact h

end FieldValuedPoints

end AlgebraicGeometry
