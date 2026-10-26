/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
  Andrew Yang (native projective-spectrum chart construction in mathlib)
Copyright (c) 2024 Andrew Yang. All rights reserved.
Adapted material released under Apache 2.0, as in mathlib's LICENSE.
-/
module

public import ProjectiveSpace.GlobalSections

@[expose] public section

set_option warningAsError true

/-!
# Unit scaling of Proj morphisms

Degree-weighted multiplication by a global unit preserves the **whole** morphism to `Proj`
constructed using a geometric cover by positive homogeneous basic opens. Comparison takes
place in the sections of the same source open, not in the two ordinary localizations of its
global section ring, which need not coincide definitionally.
-/

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization TopologicalSpace

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Evaluate degree-zero homogeneous fractions in a ring where the denominator is a unit. -/
noncomputable def awayMapOfIsUnit {R : Type u} [CommRing R] (f : A →+* R)
    {t : A} (hunit : IsUnit (f t)) : Away 𝒜 t →+* R :=
  (IsLocalization.Away.lift t hunit).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- The value of a homogeneous fraction is characterized without requiring an inverse
operation on the target ring. -/
lemma awayMapOfIsUnit_mk_spec {R : Type u} [CommRing R] (f : A →+* R)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hunit : IsUnit (f t))
    (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) :
    f a = (f t)^k * awayMapOfIsUnit 𝒜 f hunit (Away.mk 𝒜 ht k a ha) := by
  let hpow : ∀ s : Submonoid.powers t, IsUnit (f s) := fun s => by
    obtain ⟨m, hm⟩ := s.2
    rw [← hm, map_pow]
    exact hunit.pow m
  have h := (IsLocalization.lift_mk'_spec (M := Submonoid.powers t)
    (S := Localization.Away t) (g := f)
    hpow a ((IsLocalization.lift hpow)
       (IsLocalization.mk' (Localization.Away t) a ⟨t ^ k, by exact ⟨k, rfl⟩⟩))
    ⟨t ^ k, by exact ⟨k, rfl⟩⟩).mp rfl
  simpa only [awayMapOfIsUnit, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk', map_pow, IsLocalization.Away.lift] using h

/-- Two degree-weighted evaluations agree on the whole degree-zero localization,
including zero rings and nilpotent/empty charts. -/
lemma awayMapOfIsUnit_eq_of_unitScaling {R : Type u} [CommRing R]
    (f g : A →+* R) (unit : Rˣ)
    (hscale : ∀ d (a : A), a ∈ 𝒜 d → g a = (unit : R) ^ d * f a)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hunit : IsUnit (f t)) :
    awayMapOfIsUnit 𝒜 f hunit =
      awayMapOfIsUnit 𝒜 g (by
        rw [hscale d t ht]
        exact ((Units.isUnit unit).pow d).mul hunit) := by
  have hunitg : IsUnit (g t) := by
    rw [hscale d t ht]
    exact ((Units.isUnit unit).pow d).mul hunit
  change awayMapOfIsUnit 𝒜 f hunit = awayMapOfIsUnit 𝒜 g hunitg
  apply RingHom.ext
  intro z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht z
  have hf := awayMapOfIsUnit_mk_spec 𝒜 f ht hunit k a ha
  have hg := awayMapOfIsUnit_mk_spec 𝒜 g ht hunitg k a ha
  have hnum : g a = (unit : R)^(k * d) * f a := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using hscale (k • d) a ha
  have hden : (g t)^k = (unit : R)^(k * d) * (f t)^k := by
    rw [hscale d t ht, mul_pow, ← pow_mul, mul_comm d k]
  apply (hunitg.pow k).mul_left_cancel
  calc
    (g t)^k * awayMapOfIsUnit 𝒜 f hunit (Away.mk 𝒜 ht k a ha) =
        ((unit : R)^(k * d) * (f t)^k) *
          awayMapOfIsUnit 𝒜 f hunit (Away.mk 𝒜 ht k a ha) := by rw [hden]
    _ = (unit : R)^(k * d) * f a := by rw [mul_assoc, ← hf]
    _ = g a := hnum.symm
    _ = (g t)^k * awayMapOfIsUnit 𝒜 g hunitg (Away.mk 𝒜 ht k a ha) := hg

variable {X : Scheme.{u}} (f g : A →+* Γ(X, ⊤)) (unit : Γ(X, ⊤)ˣ)
variable (hscale : ∀ d (a : A), a ∈ 𝒜 d →
  g a = (unit : Γ(X, ⊤)) ^ d * f a)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Degree-weighted unit scaling preserves the source basic open of each homogeneous
element, even when the basic open is empty. -/
lemma basicOpen_eq_of_unitScaling
    (hscale : ∀ d (a : A), a ∈ 𝒜 d → g a = (unit : Γ(X, ⊤)) ^ d * f a)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) :
    X.basicOpen (g t) = X.basicOpen (f t) := by
  rw [hscale d t ht, X.basicOpen_mul,
    X.basicOpen_of_isUnit ((Units.isUnit unit).pow d)]
  simp

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The geometric positive-homogeneous cover transfers under unit scaling. -/
lemma isOpenCover_of_unitScaling
    (hscale : ∀ d (a : A), a ∈ 𝒜 d → g a = (unit : Γ(X, ⊤)) ^ d * f a)
    (hcover : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (f ir.2.1))) :
    IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (g ir.2.1)) := by
  change (⨆ ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d,
    X.basicOpen (g ir.2.1)) = ⊤
  calc
    (⨆ ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d, X.basicOpen (g ir.2.1)) =
        ⨆ ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d, X.basicOpen (f ir.2.1) := by
      apply iSup_congr
      intro ir
      exact basicOpen_eq_of_unitScaling 𝒜 f g unit hscale ir.2.2.2
    _ = ⊤ := hcover

set_option backward.isDefEq.respectTransparency.types false in
private lemma chart_source_iso (x : Γ(X, ⊤)) :
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫
      X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (basicOpenIsoSpecAway x).hom =
      (X.basicOpen x).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift x (by
          change IsUnit ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen x)) x)
          exact X.toRingedSpace.isUnit_res_basicOpen x))) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, ⊤) (Localization.Away x))))]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  change _ = (X.basicOpen x).toSpecΓ ≫
    Spec.map (X.presheaf.map (homOfLE le_top).op)
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  simp only [Scheme.isoOfEq_inv, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc]

private noncomputable def chartSectionMap {t : A} :
    Away 𝒜 t →+* Γ(X, X.basicOpen (f t)) :=
  (IsLocalization.Away.lift (f t)
    (show IsUnit ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))) (f t)) from
      X.toRingedSpace.isUnit_res_basicOpen (f t))).comp
    ((IsLocalization.map (M := .powers t) (T := .powers (f t))
      (Localization.Away (f t)) f (by
      rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t)))

private lemma chartSectionMap_eq_awayMap {t : A} :
    chartSectionMap 𝒜 f (t := t) =
      awayMapOfIsUnit 𝒜
        ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))).comp f)
        (show IsUnit ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))) (f t)) from
          X.toRingedSpace.isUnit_res_basicOpen (f t)) := by
  unfold chartSectionMap awayMapOfIsUnit
  rw [← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  rw [RingHom.comp_assoc, IsLocalization.map_comp, ← RingHom.comp_assoc,
    IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]

private noncomputable def chart {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (X.basicOpen (f t)).toScheme ⟶ Spec ↧(Away 𝒜 t) :=
  toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (basicOpenIsoSpec 𝒜 t ht hd).hom

set_option backward.isDefEq.respectTransparency.types false in
private lemma chart_spec_eq {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    chart 𝒜 f hd ht =
      (X.basicOpen (f t)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (chartSectionMap 𝒜 f (t := t))) := by
  unfold chart toBasicOpenOfGlobalSections chartSectionMap
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let phi : Away 𝒜 t →+* Localization.Away (f t) :=
    (IsLocalization.map (M := .powers t) (T := .powers (f t))
      (Localization.Away (f t)) f (by
      rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t))
  have h := congrArg (· ≫ Spec.map (CommRingCat.ofHom phi))
    (chart_source_iso (X := X) (f t))
  simpa only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    RingHom.comp_assoc] using h

set_option backward.isDefEq.respectTransparency.types false in
private lemma chart_spec_eq_on (U : X.Opens) {t : A} {d : ℕ}
    (hd : 0 < d) (ht : t ∈ 𝒜 d) (hU : U = X.basicOpen (f t))
    (hunit : IsUnit ((X.presheaf.map (homOfLE le_top).op).hom (f t) : Γ(X, U))) :
    (X.isoOfEq hU).hom ≫ chart 𝒜 f hd ht =
      U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayMapOfIsUnit 𝒜
        ((X.presheaf.map (homOfLE le_top).op).hom.comp f) hunit)) := by
  subst U
  simpa only [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp] using
    (chart_spec_eq 𝒜 f hd ht).trans (by rw [chartSectionMap_eq_awayMap])

private lemma awayMap_restrict_eq_of_unitScaling (U : X.Opens)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hunit : IsUnit ((X.presheaf.map (homOfLE le_top).op).hom (f t) : Γ(X, U))) :
    awayMapOfIsUnit 𝒜
      ((X.presheaf.map (homOfLE le_top).op).hom.comp f) hunit =
    awayMapOfIsUnit 𝒜
      ((X.presheaf.map (homOfLE le_top).op).hom.comp g)
      (by
        let res : Γ(X, ⊤) →+* Γ(X, U) :=
          (X.presheaf.map (homOfLE le_top).op).hom
        change IsUnit (res (g t))
        rw [hscale d t ht, map_mul, map_pow]
        exact ((Units.isUnit unit).map res.toMonoidHom |>.pow d).mul hunit) := by
  let res : Γ(X, ⊤) →+* Γ(X, U) := (X.presheaf.map (homOfLE le_top).op).hom
  let unitU : Γ(X, U)ˣ := Units.map res.toMonoidHom unit
  have hscaleU : ∀ n (a : A), a ∈ 𝒜 n →
      (res.comp g) a = (unitU : Γ(X, U))^n * (res.comp f) a := by
    intro n a ha
    change res (g a) = (res (unit : Γ(X, ⊤)))^n * res (f a)
    simpa only [map_pow, map_mul] using
      congrArg res (hscale n a ha)
  exact awayMapOfIsUnit_eq_of_unitScaling 𝒜 (res.comp f) (res.comp g)
    unitU hscaleU ht hunit

set_option backward.isDefEq.respectTransparency.types false in
/-- The native affine-chart morphisms agree after transporting their source basic
opens along the equality induced by degree-weighted unit scaling. -/
lemma toBasicOpenOfGlobalSections_eq_of_unitScaling
    (hscale : ∀ n (a : A), a ∈ 𝒜 n →
      g a = (unit : Γ(X, ⊤)) ^ n * f a)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      (X.isoOfEq (basicOpen_eq_of_unitScaling 𝒜 f g unit hscale ht).symm).hom ≫
        toBasicOpenOfGlobalSections 𝒜 g rfl hd ht := by
  let U : X.Opens := X.basicOpen (f t)
  have hUg : U = X.basicOpen (g t) :=
    (basicOpen_eq_of_unitScaling 𝒜 f g unit hscale ht).symm
  have hunitf : IsUnit ((X.presheaf.map (homOfLE le_top).op).hom (f t) : Γ(X, U)) :=
    X.toRingedSpace.isUnit_res_basicOpen (f t)
  have hunitg : IsUnit ((X.presheaf.map (homOfLE le_top).op).hom (g t) : Γ(X, U)) := by
    rw [hUg]
    exact X.toRingedSpace.isUnit_res_basicOpen (g t)
  have Hf := chart_spec_eq_on 𝒜 f U hd ht rfl hunitf
  have Hg := chart_spec_eq_on 𝒜 g U hd ht hUg hunitg
  have Hmap : awayMapOfIsUnit 𝒜
      ((X.presheaf.map (homOfLE le_top).op).hom.comp f) hunitf =
      awayMapOfIsUnit 𝒜
        ((X.presheaf.map (homOfLE le_top).op).hom.comp g) hunitg :=
    awayMap_restrict_eq_of_unitScaling 𝒜 f g unit hscale U ht hunitf
  have H : (X.isoOfEq (rfl : U = X.basicOpen (f t))).hom ≫ chart 𝒜 f hd ht =
      (X.isoOfEq hUg).hom ≫ chart 𝒜 g hd ht := by
    rw [Hf, Hg, Hmap]
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t ht hd).hom]
  simpa only [chart, Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    Category.assoc] using H

set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-weighted multiplication of homogeneous global sections by a unit leaves the
entire geometrically constructed `Proj` morphism unchanged. This statement does not depend
on which witnesses of the geometric cover are chosen for either morphism. -/
lemma fromOfGlobalSectionsOfIsOpenCover_eq_of_unitScaling
    (hscale : ∀ n (a : A), a ∈ 𝒜 n →
      g a = (unit : Γ(X, ⊤)) ^ n * f a)
    (hcoverf : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (f ir.2.1)))
    (hcoverg : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (g ir.2.1))) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg := by
  let cover := openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf
  refine cover.hom_ext _ _ (fun ir ↦ ?_)
  obtain ⟨d, t, hd, ht⟩ := ir
  change (X.basicOpen (f t)).ι ≫ fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
    (X.basicOpen (f t)).ι ≫ fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg
  have hleft : (X.basicOpen (f t)).ι ≫
      fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (basicOpen 𝒜 t).ι := by
    change (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf).f ⟨d, t, hd, ht⟩ ≫ _ = _
    exact (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf).ι_glueMorphisms
      _ _ ⟨d, t, hd, ht⟩
  have hright : (X.basicOpen (g t)).ι ≫
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg =
      toBasicOpenOfGlobalSections 𝒜 g rfl hd ht ≫ (basicOpen 𝒜 t).ι := by
    change (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg).f ⟨d, t, hd, ht⟩ ≫ _ = _
    exact (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg).ι_glueMorphisms
      _ _ ⟨d, t, hd, ht⟩
  have heq : X.basicOpen (f t) = X.basicOpen (g t) :=
    (basicOpen_eq_of_unitScaling 𝒜 f g unit hscale ht).symm
  calc
    _ = toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (basicOpen 𝒜 t).ι := hleft
    _ = ((X.isoOfEq heq).hom ≫ toBasicOpenOfGlobalSections 𝒜 g rfl hd ht) ≫
        (basicOpen 𝒜 t).ι := by
      rw [toBasicOpenOfGlobalSections_eq_of_unitScaling 𝒜 f g unit hscale hd ht]
    _ = (X.isoOfEq heq).hom ≫ (X.basicOpen (g t)).ι ≫
        fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg := by
      rw [Category.assoc, hright]
    _ = (X.basicOpen (f t)).ι ≫
        fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg := by
      rw [Scheme.isoOfEq_hom_ι_assoc]

/-- A single geometric cover for `f` suffices to construct and compare both arrows. -/
lemma fromOfGlobalSectionsOfIsOpenCover_unitScaling
    (hscale : ∀ n (a : A), a ∈ 𝒜 n →
      g a = (unit : Γ(X, ⊤)) ^ n * f a)
    (hcover : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (f ir.2.1))) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover =
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g
        (isOpenCover_of_unitScaling 𝒜 f g unit hscale hcover) :=
  fromOfGlobalSectionsOfIsOpenCover_eq_of_unitScaling 𝒜 f g unit hscale hcover _

end AlgebraicGeometry.Proj
