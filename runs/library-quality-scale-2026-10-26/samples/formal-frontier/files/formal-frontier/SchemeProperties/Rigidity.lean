/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GlobalSections
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Connected.Clopen

/-!
# Rigidity from a collapsed fibre

A morphism from the product of a proper integral pointed scheme over a field
with a preconnected parameter scheme to a relatively separated target factors
through the parameter if the point-image of one projection fibre is subsingleton.
The parameter scheme need not be reduced, and its distinguished point need
not be closed or rational.

The proof first obtains scheme equality near a collapsed fibre using flat base
change for global sections and an affine target. It propagates this local
statement using the closed scheme equalizer and the openness of the projection,
then concludes by open-local equality of scheme morphisms.

## References

* J. S. Milne, *Abelian Varieties*, Chapter I, Theorem 1.1, for the rigidity
  problem and the proper-neighborhood/affine-target argument.
* Mathlib's flat base change for sections on qcqs opens, relative scheme
  equalizers, and open-local morphism extensionality.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- In a cartesian square, global sections form the canonical ring pushout
when the bottom morphism is flat, the base and its change are affine, and the
other source is quasi-compact and quasi-separated. -/
lemma isPushout_appTop_of_flat
    {X W S T : Scheme.{u}} {a : W ⟶ X} {π : W ⟶ T}
    {p : X ⟶ S} {q : T ⟶ S} (H : IsPullback a π p q)
    [IsAffine S] [IsAffine T] [CompactSpace X] [QuasiSeparatedSpace X] [Flat q] :
    IsPushout p.appTop q.appTop a.appTop π.appTop := by
  have h : IsIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
      (by simp) (by simp) (by simp)) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
      (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _)
      CompactSpace.isCompact_univ isQuasiSeparated_univ
  have h' := (isIso_pushoutSection_iff H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)).mp h
  simpa only [app_eq_appLE, preimage_top, inf_idem] using h'

private lemma section_apply {W Y : Scheme.{u}} {π : W ⟶ Y}
    {σ : Y ⟶ W} (hσ : σ ≫ π = 𝟙 Y) (y : Y) : π (σ y) = y := by
  simpa only [Scheme.Hom.comp_base, Scheme.Hom.id_base, TopCat.comp_app,
    TopCat.id_app] using congrArg (fun k : Y ⟶ Y => k.base y) hσ

/-- The residue-field fibre inherits scheme equality from collapse of its
point-image. The affine constancy input is used after base change, without any
integrality assumption on that base change. -/
private lemma eq_on_fiber_of_subsingleton_image
    {K : Type u} [Field K] {X W Y Z : Scheme.{u}}
    {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of K)}
    {a : W ⟶ X} {π : W ⟶ Y} (H : IsPullback a π p q)
    [CompactSpace X] [QuasiSeparatedSpace X] [IsIso p.appTop]
    (σ : Y ⟶ W) (hσ : σ ≫ π = 𝟙 Y) (h : W ⟶ Z) (y : Y)
    (hc : (h '' (π ⁻¹' {y})).Subsingleton) :
    π.fiberι y ≫ h = π.fiberι y ≫ π ≫ σ ≫ h := by
  let ι : π.fiber y ⟶ W := π.fiberι y
  let ρ : π.fiber y ⟶ Spec (Y.residueField y) := π.fiberToSpecResidueField y
  have Hy : IsPullback (ι ≫ a) ρ p (Y.fromSpecResidueField y ≫ q) :=
    (IsPullback.of_hasPullback π (Y.fromSpecResidueField y)).paste_horiz H
  let : IsIso ρ.appTop := (isPushout_appTop_of_flat Hy).isIso_inr_of_isIso
  let τ : Spec (Y.residueField y) ⟶ π.fiber y :=
    pullback.lift (Y.fromSpecResidueField y ≫ σ) (𝟙 _)
      (by simp [Category.assoc, hσ])
  have hτρ : τ ≫ ρ = 𝟙 _ := by
    exact pullback.lift_snd (C := Scheme.{u}) (f := π)
      (g := Y.fromSpecResidueField y) (Y.fromSpecResidueField y ≫ σ)
      (𝟙 (Spec (Y.residueField y))) (by simp [Category.assoc, hσ])
  have hτι : τ ≫ ι = Y.fromSpecResidueField y ≫ σ := by
    exact pullback.lift_fst (C := Scheme.{u}) (f := π)
      (g := Y.fromSpecResidueField y) (Y.fromSpecResidueField y ≫ σ)
      (𝟙 (Spec (Y.residueField y))) (by simp [Category.assoc, hσ])
  obtain ⟨U, hU, hzU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
      (x := h (σ y)) (by trivial)
  let : IsAffine U := hU
  have hσy : σ y ∈ π ⁻¹' {y} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using section_apply hσ y
  have hrange : Set.range (ι ≫ h) ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    have hw : ι w ∈ π ⁻¹' {y} := by
      rw [← π.range_fiberι y]
      exact ⟨w, rfl⟩
    have he : h (ι w) = h (σ y) := hc ⟨ι w, hw, rfl⟩ ⟨σ y, hσy, rfl⟩
    refine ⟨⟨h (ι w), ?_⟩, rfl⟩
    rw [he]
    exact hzU
  let hU' : π.fiber y ⟶ U := IsOpenImmersion.lift U.ι (ι ≫ h) hrange
  have hfac : ι ≫ h = ρ ≫ τ ≫ ι ≫ h := by
    have he := congrArg (fun k : π.fiber y ⟶ U => k ≫ U.ι)
      (eq_comp_section_of_isIso_appTop ρ τ hτρ hU')
    simpa only [Category.assoc, hU', IsOpenImmersion.lift_fac] using he
  change ι ≫ h = ι ≫ π ≫ σ ≫ h
  calc
    ι ≫ h = ρ ≫ τ ≫ ι ≫ h := hfac
    _ = ρ ≫ (Y.fromSpecResidueField y ≫ σ) ≫ h := by
      rw [← Category.assoc τ ι h, hτι]
    _ = (ρ ≫ Y.fromSpecResidueField y) ≫ σ ≫ h := by simp only [Category.assoc]
    _ = ι ≫ π ≫ σ ≫ h := by
      have hιρ : ι ≫ π = ρ ≫ Y.fromSpecResidueField y := π.fiber_fac y
      rw [← hιρ]
      simp only [Category.assoc]

/-- Proper shrinking places the inverse image of an affine neighborhood in
an affine target, where the equality is an equality of scheme morphisms. -/
private lemma eq_on_neighborhood_of_subsingleton_image
    {K : Type u} [Field K] {X W Y Z : Scheme.{u}}
    {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of K)}
    {a : W ⟶ X} {π : W ⟶ Y} (H : IsPullback a π p q)
    [CompactSpace X] [QuasiSeparatedSpace X] [IsIso p.appTop] [UniversallyClosed π]
    (σ : Y ⟶ W) (hσ : σ ≫ π = 𝟙 Y) (h : W ⟶ Z) (y : Y)
    (hc : (h '' (π ⁻¹' {y})).Subsingleton) :
    ∃ T : Y.Opens, y ∈ T ∧
      (π ⁻¹ᵁ T).ι ≫ h = (π ⁻¹ᵁ T).ι ≫ π ≫ σ ≫ h := by
  classical
  obtain ⟨U, hU, hzU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
      (x := h (σ y)) (by trivial)
  let : IsAffine U := hU
  let C : Set W := h ⁻¹' (U : Set Z)ᶜ
  have hC : IsClosed C := U.2.isClosed_compl.preimage h.continuous
  let N : Y.Opens := ⟨(π '' C)ᶜ, (π.isClosedMap C hC).isOpen_compl⟩
  have hσy : σ y ∈ π ⁻¹' {y} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using section_apply hσ y
  have hyN : y ∈ N := by
    rintro ⟨w, hwC, hwy⟩
    have hw : w ∈ π ⁻¹' {y} := hwy
    have he : h w = h (σ y) := hc ⟨w, hw, rfl⟩ ⟨σ y, hσy, rfl⟩
    apply hwC
    change h w ∈ U
    rw [he]
    exact hzU
  have hN : ∀ w : W, π w ∈ N → h w ∈ U := by
    intro w hw
    by_contra hnot
    exact hw ⟨w, hnot, rfl⟩
  obtain ⟨T, hT, hyT, hTN⟩ := exists_isAffineOpen_mem_and_subset hyN
  let : IsAffine T := hT
  let v : (π ⁻¹ᵁ T).toScheme ⟶ W := (π ⁻¹ᵁ T).ι
  let πT : (π ⁻¹ᵁ T).toScheme ⟶ T := π ∣_ T
  have HT : IsPullback (v ≫ a) πT p (T.ι ≫ q) :=
    (isPullback_morphismRestrict π T).flip.paste_horiz H
  let : IsIso πT.appTop := (isPushout_appTop_of_flat HT).isIso_inr_of_isIso
  have hσrange : Set.range (T.ι ≫ σ) ⊆ Set.range v := by
    rintro _ ⟨t, rfl⟩
    refine ⟨⟨σ (T.ι t), ?_⟩, rfl⟩
    change π (σ (T.ι t)) ∈ T
    rw [section_apply hσ]
    exact t.property
  let σT : T.toScheme ⟶ (π ⁻¹ᵁ T).toScheme :=
    IsOpenImmersion.lift v (T.ι ≫ σ) hσrange
  have hσTv : σT ≫ v = T.ι ≫ σ :=
    IsOpenImmersion.lift_fac v (T.ι ≫ σ) hσrange
  have hσTπ : σT ≫ πT = 𝟙 T.toScheme := by
    apply (cancel_mono T.ι).mp
    rw [Category.assoc]
    change σT ≫ (π ∣_ T ≫ T.ι) = (𝟙 T.toScheme) ≫ T.ι
    rw [morphismRestrict_ι]
    change σT ≫ v ≫ π = (𝟙 T.toScheme) ≫ T.ι
    rw [← Category.assoc, hσTv, Category.assoc, hσ]
    simp
  have hhrange : Set.range (v ≫ h) ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    have hwT : π (v w) ∈ T := w.property
    have hwU : h (v w) ∈ U := hN (v w) (hTN hwT)
    exact ⟨⟨h (v w), hwU⟩, rfl⟩
  let b : (π ⁻¹ᵁ T).toScheme ⟶ U := IsOpenImmersion.lift U.ι (v ≫ h) hhrange
  have hb : v ≫ h = πT ≫ σT ≫ v ≫ h := by
    have he := congrArg (fun k : (π ⁻¹ᵁ T).toScheme ⟶ U => k ≫ U.ι)
      (eq_comp_section_of_isIso_appTop πT σT hσTπ b)
    simpa only [Category.assoc, b, IsOpenImmersion.lift_fac] using he
  refine ⟨T, hyT, ?_⟩
  change v ≫ h = v ≫ π ≫ σ ≫ h
  calc
    v ≫ h = πT ≫ σT ≫ v ≫ h := hb
    _ = πT ≫ (T.ι ≫ σ) ≫ h := by rw [← Category.assoc σT v h, hσTv]
    _ = (πT ≫ T.ι) ≫ σ ≫ h := by simp only [Category.assoc]
    _ = v ≫ π ≫ σ ≫ h := by
      change (π ∣_ T ≫ T.ι) ≫ σ ≫ h = v ≫ π ≫ σ ≫ h
      rw [morphismRestrict_ι]
      simp only [v, Category.assoc]

/-- Relative rigidity from the subsingleton image of one topological fibre.

The unique factor is over the same field. Neither the parameter scheme nor
its product with the proper factor is required to be reduced, and the supplied
parameter point need not be rational or closed. -/
lemma existsUnique_factor_through_snd_of_subsingleton_fiber_image
    (K : Type u) [Field K] (X Y Z : Scheme.{u})
    (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K)) (r : Z ⟶ Spec (.of K))
    [IsProper p] [IsIntegral X] [PreconnectedSpace Y] [IsSeparated r]
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ p = 𝟙 _)
    (h : pullback p q ⟶ Z) (hh : h ≫ r = pullback.snd p q ≫ q)
    (y₀ : Y) (hc : (h '' ((pullback.snd p q) ⁻¹' {y₀})).Subsingleton) :
    ∃! (g : Y ⟶ Z), g ≫ r = q ∧ h = pullback.snd p q ≫ g := by
  classical
  let π : pullback p q ⟶ Y := pullback.snd p q
  let σ : Y ⟶ pullback p q :=
    pullback.lift (q ≫ x₀) (𝟙 Y) (by simp [Category.assoc, hx₀])
  have hσ : σ ≫ π = 𝟙 Y := by simp only [σ, π, pullback.lift_snd]
  let H : IsPullback (pullback.fst p q) π p q := IsPullback.of_hasPullback p q
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  let : IsIso p.appTop := isIso_appTop_of_universallyClosed_of_section p x₀ hx₀
  let f : pullback p q ⟶ Z := π ≫ σ ≫ h
  let WB : Over (Spec (.of K)) := Over.mk (π ≫ q)
  let ZB : Over (Spec (.of K)) := Over.mk r
  let hB : WB ⟶ ZB := Over.homMk h hh
  let fB : WB ⟶ ZB := Over.homMk f (by
    change (π ≫ σ ≫ h) ≫ r = π ≫ q
    simp only [Category.assoc, hh]
    rw [← Category.assoc σ π q, hσ, Category.id_comp])
  let e : (equalizer hB fB).left ⟶ pullback (C := Scheme) p q :=
    (equalizer.ι hB fB).left
  let E : Set (pullback (C := Scheme) p q) := Set.range e.base
  have hE : IsClosed E := by
    have : IsSeparated ZB.hom := ‹IsSeparated r›
    have : IsClosedImmersion e := isClosedImmersion_equalizer_ι_left hB fB
    exact e.isClosedEmbedding.isClosed_range
  have he : e ≫ h = e ≫ f :=
    congrArg (fun k : equalizer hB fB ⟶ ZB => k.left) (equalizer.condition hB fB)
  have factor_range (V : Scheme.{u}) (j : V ⟶ pullback p q)
      (hj : j ≫ h = j ≫ f) : Set.range j ⊆ E := by
    let jB : Over.mk (j ≫ (π ≫ q)) ⟶ WB := Over.homMk j (by rfl)
    have hjB : jB ≫ hB = jB ≫ fB := by
      apply Over.OverMorphism.ext
      exact hj
    have hl : (equalizer.lift jB hjB).left ≫ e = j :=
      congrArg (fun k : Over.mk (j ≫ (π ≫ q)) ⟶ WB => k.left)
        (equalizer.lift_ι jB hjB)
    rintro _ ⟨v, rfl⟩
    refine ⟨(equalizer.lift jB hjB).left v, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : V ⟶ pullback p q => k v) hl
  have he_point (w : pullback (C := Scheme) p q) (hw : w ∈ E) : h w = f w := by
    obtain ⟨v, rfl⟩ := hw
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : (equalizer hB fB).left ⟶ Z => k v) he
  let S : Set Y := {y | π ⁻¹' {y} ⊆ E}
  have collapse_of_mem (y : Y) (hy : y ∈ S) : (h '' (π ⁻¹' {y})).Subsingleton := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    calc
      h w = f w := he_point w (hy hw)
      _ = f w' := by
        simp only [f, Scheme.Hom.comp_apply]
        rw [show π w = y from hw, show π w' = y from hw']
      _ = h w' := (he_point w' (hy hw')).symm
  have hy₀ : y₀ ∈ S := by
    have hfib := eq_on_fiber_of_subsingleton_image H σ hσ h y₀ hc
    have hrange : Set.range (π.fiberι y₀) ⊆ E :=
      factor_range _ _ (by simpa only [f, Category.assoc] using hfib)
    intro w hw
    apply hrange
    rw [π.range_fiberι y₀]
    exact hw
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨T, hyT, hT⟩ := eq_on_neighborhood_of_subsingleton_image
      H σ hσ h y (collapse_of_mem y hy)
    have hTE : Set.range (π ⁻¹ᵁ T).ι ⊆ E :=
      factor_range _ _ (by simpa only [f, Category.assoc] using hT)
    apply Filter.mem_of_superset (T.2.mem_nhds hyT)
    intro z hz w hw
    have hwT : w ∈ π ⁻¹ᵁ T := by
      change π w ∈ T
      rw [show π w = z from hw]
      exact hz
    exact hTE ⟨⟨w, hwT⟩, rfl⟩
  have hScompl : Sᶜ = π '' Eᶜ := by
    ext y
    constructor
    · intro hy
      simp only [S, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.subset_def,
        Set.mem_preimage, Set.mem_singleton_iff, not_forall] at hy
      obtain ⟨w, hw, hwE⟩ := hy
      exact ⟨w, hwE, hw⟩
    · rintro ⟨w, hw, rfl⟩ hy
      exact hw (hy (by simp))
  have hSclosed : IsClosed S := by
    apply isOpen_compl_iff.mp
    rw [hScompl]
    exact π.isOpenMap _ hE.isOpen_compl
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ ⟨y₀, hy₀⟩
  have hglobal : h = f := by
    apply Scheme.hom_ext_of_forall
    intro w
    have hπw : π w ∈ S := by rw [hSuniv]; trivial
    obtain ⟨T, hwT, hT⟩ := eq_on_neighborhood_of_subsingleton_image
      H σ hσ h (π w) (collapse_of_mem (π w) hπw)
    exact ⟨π ⁻¹ᵁ T, hwT, by simpa only [f, Category.assoc] using hT⟩
  refine ⟨σ ≫ h, ⟨?_, hglobal⟩, ?_⟩
  · calc
      (σ ≫ h) ≫ r = σ ≫ (π ≫ q) := by rw [Category.assoc, hh]
      _ = q := by rw [← Category.assoc, hσ]; simp
  · intro g hg
    have hg' : σ ≫ h = g := by
      rw [hg.2, ← Category.assoc, hσ, Category.id_comp]
    exact hg'.symm

end AlgebraicGeometry.Scheme.Hom
