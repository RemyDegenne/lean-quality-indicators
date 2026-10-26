/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.QuasiFlasqueAcyclicity
public import SheafCohomology.DegreeZero
public import SheafCohomology.AcyclicResolution
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.Algebra.Homology.Functor

public section

/-!
# A functorial flasque resolution

This file constructs the canonical stalk-skyscraper flasque envelope of an
abelian sheaf, iterates its cokernel, and packages the resulting maps as an
augmented cochain complex.  The augmentation is a quasi-isomorphism and every
term is flasque.  On compact prespectral quasi-separated spaces, positive
degree sheaf cohomology is compared with the homology of global sections of
this resolution.  The one-step dimension-shift comparison is natural in the
input sheaf.

The construction currently uses a common universe for the space, sheaves, and
Ext groups.  It does not provide independently varying universe parameters.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

private theorem isFlasque_of_iso {F G : Presheaf AddCommGrpCat X}
    (e : F ≅ G) [TopCat.Presheaf.IsFlasque F] : TopCat.Presheaf.IsFlasque G where
  epi {U V} r := by
    let _ : Epi (F.map r) := TopCat.Presheaf.IsFlasque.epi r
    let _ : IsIso (e.hom.app V) := by infer_instance
    have h : Epi (F.map r ≫ e.hom.app V) := inferInstance
    rw [e.hom.naturality r] at h
    exact CategoryTheory.epi_of_epi (e.hom.app U) (G.map r)

/-- The stalk-skyscraper endofunctor at a point. -/
abbrev stalkSkyscraperFunctor (x : X) :
    Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X :=
  Sheaf.forget AddCommGrpCat X ⋙
    Presheaf.stalkFunctor AddCommGrpCat x ⋙
      skyscraperSheafFunctor x

/-- The product of the stalk-skyscraper endofunctors over all points. -/
noncomputable abbrev flasqueEnvelopeFunctor :
    Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X :=
  ∏ᶜ fun x : X => stalkSkyscraperFunctor x

/-- The adjunction units assemble to a natural map into the flasque envelope. -/
noncomputable abbrev toFlasqueEnvelope :
    𝟭 (Sheaf AddCommGrpCat X) ⟶ flasqueEnvelopeFunctor :=
  Pi.lift fun x => (stalkSkyscraperSheafAdjunction x).unit

noncomputable instance (F : Sheaf AddCommGrpCat X) :
    TopCat.Sheaf.IsFlasque (flasqueEnvelopeFunctor.obj F) := by
  let family : X → (Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X) :=
    fun x => stalkSkyscraperFunctor x
  let _ : ∀ x : X, TopCat.Sheaf.IsFlasque ((family x).obj F) := fun x => by
    dsimp [family, stalkSkyscraperFunctor]
    exact isFlasque_skyscraperSheaf_of_hasZeroObject x _
  let _ : TopCat.Presheaf.IsFlasque
      ((Sheaf.forget AddCommGrpCat X).obj
        (∏ᶜ fun x : X => (family x).obj F)) :=
    TopCat.Sheaf.IsFlasque.product _
  exact isFlasque_of_iso
    ((Sheaf.forget AddCommGrpCat X).mapIso (piObjIso family F).symm)

noncomputable instance toFlasqueEnvelope_app_mono
    (F : Sheaf AddCommGrpCat X) : Mono (toFlasqueEnvelope.app F) := by
  let hStalkMono (x : X) :
      Mono ((Presheaf.stalkFunctor AddCommGrpCat x).map
        (toFlasqueEnvelope.app F).hom) := by
    change Mono ((Sheaf.forget AddCommGrpCat X ⋙
      Presheaf.stalkFunctor AddCommGrpCat x).map
        (toFlasqueEnvelope.app F))
    have hUnit :
        toFlasqueEnvelope.app F ≫
            (Pi.π (fun y : X => stalkSkyscraperFunctor y) x).app F =
          (stalkSkyscraperSheafAdjunction x).unit.app F := by
      exact congr_app
        (CategoryTheory.Limits.Pi.lift_π
          (fun x => (stalkSkyscraperSheafAdjunction x).unit) x) F
    have h :
        (Sheaf.forget AddCommGrpCat X ⋙
            Presheaf.stalkFunctor AddCommGrpCat x).map
            (toFlasqueEnvelope.app F) ≫
          (Sheaf.forget AddCommGrpCat X ⋙
            Presheaf.stalkFunctor AddCommGrpCat x).map
            ((Pi.π (fun y : X => stalkSkyscraperFunctor y) x).app F) ≫
          (stalkSkyscraperSheafAdjunction x).counit.app
            ((Sheaf.forget AddCommGrpCat X ⋙
              Presheaf.stalkFunctor AddCommGrpCat x).obj F) =
        𝟙 _ := by
      rw [← Category.assoc, ← (Sheaf.forget AddCommGrpCat X ⋙
        Presheaf.stalkFunctor AddCommGrpCat x).map_comp, hUnit]
      exact (stalkSkyscraperSheafAdjunction x).left_triangle_components F
    exact mono_of_mono_fac h
  exact TopCat.Presheaf.mono_of_stalk_mono _

/-- The functorial quotient by the stalk-skyscraper flasque envelope. -/
noncomputable abbrev flasqueEnvelopeQuotientFunctor :
    Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X :=
  cokernel (toFlasqueEnvelope (X := X))

/-- The natural projection onto the functorial quotient. -/
noncomputable abbrev toFlasqueEnvelopeQuotient :
    flasqueEnvelopeFunctor (X := X) ⟶
      flasqueEnvelopeQuotientFunctor (X := X) :=
  cokernel.π (toFlasqueEnvelope (X := X))

@[reassoc (attr := simp)]
theorem toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient :
    toFlasqueEnvelope (X := X) ≫
      toFlasqueEnvelopeQuotient (X := X) = 0 :=
  cokernel.condition (toFlasqueEnvelope (X := X))

noncomputable instance toFlasqueEnvelopeQuotient_app_epi
    (F : Sheaf AddCommGrpCat X) :
    Epi ((toFlasqueEnvelopeQuotient (X := X)).app F) := by
  dsimp [toFlasqueEnvelopeQuotient]
  infer_instance

/-- The first short complex in the functorial flasque resolution. -/
@[simps]
noncomputable abbrev flasqueEnvelopeShortComplexNat :
    ShortComplex
      (Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X) where
  f := toFlasqueEnvelope (X := X)
  g := toFlasqueEnvelopeQuotient (X := X)

noncomputable instance : Mono (flasqueEnvelopeShortComplexNat (X := X)).f := by
  exact NatTrans.mono_of_mono_app _

noncomputable instance : Epi (flasqueEnvelopeShortComplexNat (X := X)).g := by
  dsimp
  infer_instance

theorem flasqueEnvelopeShortExactNat :
    (flasqueEnvelopeShortComplexNat (X := X)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _
    (cokernelIsCokernel (toFlasqueEnvelope (X := X)))

/-- The first objectwise short complex in the functorial flasque resolution. -/
@[simps]
noncomputable abbrev flasqueEnvelopeShortComplex
    (F : Sheaf AddCommGrpCat X) : ShortComplex (Sheaf AddCommGrpCat X) where
  f := (toFlasqueEnvelope (X := X)).app F
  g := (toFlasqueEnvelopeQuotient (X := X)).app F
  zero := congr_app
    (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) F

theorem flasqueEnvelopeShortExact (F : Sheaf AddCommGrpCat X) :
    (flasqueEnvelopeShortComplex F).ShortExact where
  exact :=
    (ShortComplex.ShortExact.map_of_exact
      (flasqueEnvelopeShortExactNat (X := X))
      ((evaluation (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)).obj F)).exact

/-- Iterates of the quotient functor used in the functorial flasque resolution. -/
@[expose] noncomputable def flasqueEnvelopeQuotientIterate :
    ℕ → (Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X)
  | 0 => Functor.id _
  | n + 1 => flasqueEnvelopeQuotientIterate n ⋙
      flasqueEnvelopeQuotientFunctor (X := X)

@[simp]
theorem flasqueEnvelopeQuotientIterate_zero :
    flasqueEnvelopeQuotientIterate (X := X) 0 = Functor.id _ := rfl

@[simp]
theorem flasqueEnvelopeQuotientIterate_succ (n : ℕ) :
    flasqueEnvelopeQuotientIterate (X := X) (n + 1) =
      flasqueEnvelopeQuotientIterate (X := X) n ⋙
        flasqueEnvelopeQuotientFunctor (X := X) := rfl

/-- The degree-`n` functor in the functorial flasque resolution. -/
noncomputable abbrev flasqueResolutionFunctor (n : ℕ) :
    Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X :=
  flasqueEnvelopeQuotientIterate n ⋙ flasqueEnvelopeFunctor (X := X)

/-- The degree-`n` differential in the functorial flasque resolution. -/
@[expose] noncomputable def flasqueResolutionDifferential (n : ℕ) :
    flasqueResolutionFunctor (X := X) n ⟶
      flasqueResolutionFunctor (X := X) (n + 1) where
  app F :=
    (toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) ≫
      (toFlasqueEnvelope (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) (n + 1)).obj F)
  naturality {F G} f := by
    change
      (flasqueEnvelopeFunctor (X := X)).map
          ((flasqueEnvelopeQuotientIterate (X := X) n).map f) ≫
        ((toFlasqueEnvelopeQuotient (X := X)).app
            ((flasqueEnvelopeQuotientIterate (X := X) n).obj G) ≫
          (toFlasqueEnvelope (X := X)).app
            ((flasqueEnvelopeQuotientFunctor (X := X)).obj
              ((flasqueEnvelopeQuotientIterate (X := X) n).obj G))) =
      ((toFlasqueEnvelopeQuotient (X := X)).app
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) ≫
        (toFlasqueEnvelope (X := X)).app
          ((flasqueEnvelopeQuotientFunctor (X := X)).obj
            ((flasqueEnvelopeQuotientIterate (X := X) n).obj F))) ≫
        (flasqueEnvelopeFunctor (X := X)).map
          ((flasqueEnvelopeQuotientFunctor (X := X)).map
            ((flasqueEnvelopeQuotientIterate (X := X) n).map f))
    rw [← Category.assoc,
      (toFlasqueEnvelopeQuotient (X := X)).naturality
        ((flasqueEnvelopeQuotientIterate (X := X) n).map f),
      Category.assoc]
    have hη := (toFlasqueEnvelope (X := X)).naturality
      ((flasqueEnvelopeQuotientFunctor (X := X)).map
        ((flasqueEnvelopeQuotientIterate (X := X) n).map f))
    simp only [Functor.id_map] at hη
    rw [hη, ← Category.assoc]

@[reassoc (attr := simp)]
theorem flasqueResolutionDifferential_comp (n : ℕ) :
    flasqueResolutionDifferential (X := X) n ≫
      flasqueResolutionDifferential (X := X) (n + 1) = 0 := by
  ext F
  change
    ((toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) ≫
      (toFlasqueEnvelope (X := X)).app
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F))) ≫
      ((toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)) ≫
        (toFlasqueEnvelope (X := X)).app
          ((flasqueEnvelopeQuotientFunctor (X := X)).obj
            ((flasqueEnvelopeQuotientFunctor (X := X)).obj
              ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)))) = 0
  rw [Category.assoc]
  rw [← Category.assoc
    ((toFlasqueEnvelope (X := X)).app
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)))
    ((toFlasqueEnvelopeQuotient (X := X)).app
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)))
    ((toFlasqueEnvelope (X := X)).app
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F))))]
  have h := congr_app
      (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X))
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F))
  change
    (toFlasqueEnvelope (X := X)).app
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)) ≫
      (toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)) = 0 at h
  rw [h, zero_comp, comp_zero]

/-- The functorial stalk-skyscraper flasque resolution, before evaluation at
a particular sheaf. -/
@[expose] noncomputable def flasqueResolutionNat :
    CochainComplex
      (Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X) ℕ where
  X := flasqueResolutionFunctor (X := X)
  d i j := if h : i + 1 = j then
      flasqueResolutionDifferential (X := X) i ≫
        eqToHom (congrArg (flasqueResolutionFunctor (X := X)) h)
    else 0
  shape i j h := by
    rw [dite_eq_right]
    exact h
  d_comp_d' i j k hij hjk := by
    change i + 1 = j at hij
    change j + 1 = k at hjk
    subst j
    subst k
    simp only [dite_eq_left, eqToHom_refl, Category.comp_id]
    exact flasqueResolutionDifferential_comp (X := X) i

/-- Evaluation of the functorial flasque resolution at a sheaf. -/
noncomputable abbrev flasqueResolution (F : Sheaf AddCommGrpCat X) :
    CochainComplex (Sheaf AddCommGrpCat X) ℕ :=
  (flasqueResolutionNat (X := X)).asFunctor.obj F

noncomputable instance flasqueResolution_isFlasque
    (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((flasqueResolution F).X n) := by
  change TopCat.Sheaf.IsFlasque
    ((flasqueEnvelopeFunctor (X := X)).obj
      ((flasqueEnvelopeQuotientIterate (X := X) n).obj F))
  infer_instance

@[simp]
theorem flasqueResolution_d_succ (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    (flasqueResolution F).d n (n + 1) =
      (toFlasqueEnvelopeQuotient (X := X)).app
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) ≫
        (toFlasqueEnvelope (X := X)).app
          ((flasqueEnvelopeQuotientIterate (X := X) (n + 1)).obj F) := by
  simp [flasqueResolution, flasqueResolutionNat,
    flasqueResolutionDifferential]
  rfl

theorem flasqueResolution_exactAt_succ
    (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    (flasqueResolution F).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [flasqueResolution_d_succ]
  simp only [flasqueEnvelopeQuotientIterate_succ, Functor.comp_obj]
  let A := (flasqueEnvelopeQuotientIterate (X := X) n).obj F
  let B := (flasqueEnvelopeQuotientFunctor (X := X)).obj A
  let C := (flasqueEnvelopeQuotientFunctor (X := X)).obj B
  have hB := congr_app
    (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) B
  change
    (toFlasqueEnvelope (X := X)).app B ≫
      (toFlasqueEnvelopeQuotient (X := X)).app B = 0 at hB
  let core := flasqueEnvelopeShortComplex B
  let middle : ShortComplex (Sheaf AddCommGrpCat X) :=
    ShortComplex.mk
      ((toFlasqueEnvelope (X := X)).app B)
      ((toFlasqueEnvelopeQuotient (X := X)).app B ≫
        (toFlasqueEnvelope (X := X)).app C)
      (by simp [← Category.assoc, hB])
  let target : ShortComplex (Sheaf AddCommGrpCat X) :=
    ShortComplex.mk
      ((toFlasqueEnvelopeQuotient (X := X)).app A ≫
        (toFlasqueEnvelope (X := X)).app B)
      ((toFlasqueEnvelopeQuotient (X := X)).app B ≫
        (toFlasqueEnvelope (X := X)).app C)
      (by
        rw [Category.assoc]
        rw [← Category.assoc
          ((toFlasqueEnvelope (X := X)).app B)
          ((toFlasqueEnvelopeQuotient (X := X)).app B)
          ((toFlasqueEnvelope (X := X)).app C)]
        rw [hB, zero_comp, comp_zero])
  change target.Exact
  let a : core ⟶ middle :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (toFlasqueEnvelope (X := X)).app C }
  let _ : Epi a.τ₁ := by dsimp [a]; infer_instance
  let _ : IsIso a.τ₂ := by dsimp [a]; infer_instance
  let _ : Mono a.τ₃ := by dsimp [a]; infer_instance
  have hmiddle : middle.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).1
      (flasqueEnvelopeShortExact B).exact
  let b : target ⟶ middle :=
    { τ₁ := (toFlasqueEnvelopeQuotient (X := X)).app A
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  let _ : Epi b.τ₁ := by dsimp [b]; infer_instance
  let _ : IsIso b.τ₂ := by dsimp [b]; infer_instance
  let _ : Mono b.τ₃ := by dsimp [b]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono b).2 hmiddle

/-- The augmented degree-zero short complex of the functorial flasque
resolution. -/
@[simps]
noncomputable abbrev flasqueResolutionAugmentedShortComplex
    (F : Sheaf AddCommGrpCat X) : ShortComplex (Sheaf AddCommGrpCat X) where
  f := (toFlasqueEnvelope (X := X)).app F
  g := (toFlasqueEnvelopeQuotient (X := X)).app F ≫
    (toFlasqueEnvelope (X := X)).app
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj F)
  zero := by
    rw [← Category.assoc]
    have h := congr_app
      (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) F
    change
      (toFlasqueEnvelope (X := X)).app F ≫
        (toFlasqueEnvelopeQuotient (X := X)).app F = 0 at h
    rw [h, zero_comp]

noncomputable instance (F : Sheaf AddCommGrpCat X) :
    Mono (flasqueResolutionAugmentedShortComplex F).f := by
  dsimp
  infer_instance

theorem flasqueResolutionAugmentedShortExact
    (F : Sheaf AddCommGrpCat X) :
    (flasqueResolutionAugmentedShortComplex F).Exact := by
  let core := flasqueEnvelopeShortComplex F
  let target := flasqueResolutionAugmentedShortComplex F
  let a : core ⟶ target :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (toFlasqueEnvelope (X := X)).app
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj F) }
  let _ : Epi a.τ₁ := by dsimp [a]; infer_instance
  let _ : IsIso a.τ₂ := by dsimp [a]; infer_instance
  let _ : Mono a.τ₃ := by dsimp [a]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).1
    (flasqueEnvelopeShortExact F).exact

/-- The augmentation from a sheaf concentrated in degree zero to its
functorial flasque resolution. -/
@[expose] noncomputable def toFlasqueResolution (F : Sheaf AddCommGrpCat X) :
    (CochainComplex.single₀ (Sheaf AddCommGrpCat X)).obj F ⟶
      flasqueResolution F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(toFlasqueEnvelope (X := X)).app F, by
      change
        (toFlasqueEnvelope (X := X)).app F ≫
          ((toFlasqueEnvelopeQuotient (X := X)).app F ≫
            (toFlasqueEnvelope (X := X)).app
              ((flasqueEnvelopeQuotientFunctor (X := X)).obj F)) = 0
      rw [← Category.assoc]
      have h := congr_app
        (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) F
      change
        (toFlasqueEnvelope (X := X)).app F ≫
          (toFlasqueEnvelopeQuotient (X := X)).app F = 0 at h
      rw [h, zero_comp]⟩

@[simp]
theorem toFlasqueResolution_f_zero (F : Sheaf AddCommGrpCat X) :
    (toFlasqueResolution F).f 0 = (toFlasqueEnvelope (X := X)).app F := by
  apply CochainComplex.fromSingle₀Equiv_symm_apply_f_zero

noncomputable instance toFlasqueResolution_quasiIso
    (F : Sheaf AddCommGrpCat X) : QuasiIso (toFlasqueResolution F) :=
  ⟨fun n => by
    cases n with
    | zero =>
        rw [CochainComplex.quasiIsoAt₀_iff,
          ShortComplex.quasiIso_iff_of_zeros]
        · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
            ⟨flasqueResolutionAugmentedShortExact F, by
              dsimp [flasqueResolutionAugmentedShortComplex]
              infer_instance⟩
          exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by
              change (toFlasqueEnvelope (X := X)).app F =
                (toFlasqueResolution F).f 0
              rw [toFlasqueResolution_f_zero])
            (by
              change
                (toFlasqueEnvelopeQuotient (X := X)).app F ≫
                    (toFlasqueEnvelope (X := X)).app
                      ((flasqueEnvelopeQuotientFunctor (X := X)).obj F) =
                  (flasqueResolution F).d 0 1
              rw [flasqueResolution_d_succ]
              rfl)
        all_goals rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt]
        · exact flasqueResolution_exactAt_succ F n
        · exact CochainComplex.exactAt_succ_single_obj F n⟩

/-- The canonical augmentations assemble naturally from sheaves concentrated
in degree zero to their functorial flasque resolutions. -/
@[expose] noncomputable def toFlasqueResolutionNat :
    CochainComplex.single₀ (Sheaf AddCommGrpCat X) ⟶
      (flasqueResolutionNat (X := X)).asFunctor where
  app F := toFlasqueResolution F
  naturality F G f := by
    ext
    change f ≫ (toFlasqueEnvelope (X := X)).app G =
      (toFlasqueEnvelope (X := X)).app F ≫
        (flasqueEnvelopeFunctor (X := X)).map f
    exact (toFlasqueEnvelope (X := X)).naturality f

end TopCat.Sheaf

namespace CategoryTheory.ShortComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If the cycles of a short complex are exhibited by a kernel `i : Q ⟶ X₂`
and the first differential factors as `p ≫ i`, then its homology is the
cokernel of `p`. -/
@[expose] noncomputable def homologyIsoCokernelOfKernelFactorization
    (S : ShortComplex C) (Q : C) (p : S.X₁ ⟶ Q) (i : Q ⟶ S.X₂)
    (hfi : p ≫ i = S.f) (hig : i ≫ S.g = 0)
    (hi : IsLimit (KernelFork.ofι i hig)) :
    S.homology ≅ cokernel p := by
  let _ : Mono i := ⟨fun _ _ h ↦ Fork.IsLimit.hom_ext hi h⟩
  have hp : hi.lift (KernelFork.ofι S.f S.zero) = p := by
    apply (cancel_mono i).1
    exact (hi.fac (KernelFork.ofι S.f S.zero)
      WalkingParallelPair.zero).trans hfi.symm
  let h : S.LeftHomologyData :=
    { K := Q
      H := cokernel p
      i := i
      π := cokernel.π p
      wi := hig
      hi := hi
      wπ := by rw [hp]; exact cokernel.condition p
      hπ := by
        apply CokernelCofork.isColimitOfIsColimitOfIff'
          (cokernelIsCokernel p)
        intro W φ
        rw [hp] }
  exact h.homologyIso

end CategoryTheory.ShortComplex

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

/-- A monomorphism of sheaves of additive commutative groups is pointwise
monic on sections. -/
noncomputable instance sheafHom_app_mono {F G : Sheaf AddCommGrpCat X}
    (f : F ⟶ G) [Mono f] (U : Opens X) : Mono (f.hom.app (op U)) := by
  change Mono (((Sheaf.forget AddCommGrpCat X).map f).app (op U))
  have hf : Mono ((Sheaf.forget AddCommGrpCat X).map f) :=
    Functor.map_mono (Sheaf.forget AddCommGrpCat X) f
  exact (NatTrans.mono_iff_mono_app _).mp hf _

/-- Three consecutive envelope terms after evaluation on the terminal open,
starting from an arbitrary sheaf `A`. -/
noncomputable abbrev flasqueEnvelopeSectionsShortComplex
    (A : Sheaf AddCommGrpCat X) : ShortComplex AddCommGrpCat where
  f := ((toFlasqueEnvelopeQuotient (X := X)).app A ≫
      (toFlasqueEnvelope (X := X)).app
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj A)).hom.app
          (op (⊤ : Opens X))
  g := ((toFlasqueEnvelopeQuotient (X := X)).app
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj A) ≫
    (toFlasqueEnvelope (X := X)).app
      ((flasqueEnvelopeQuotientFunctor (X := X)).obj
        ((flasqueEnvelopeQuotientFunctor (X := X)).obj A))).hom.app
          (op (⊤ : Opens X))
  zero := by
    let B := (flasqueEnvelopeQuotientFunctor (X := X)).obj A
    let C := (flasqueEnvelopeQuotientFunctor (X := X)).obj B
    have h := congr_app
      (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) B
    change
      (toFlasqueEnvelope (X := X)).app B ≫
        (toFlasqueEnvelopeQuotient (X := X)).app B = 0 at h
    have hs :
        ((toFlasqueEnvelopeQuotient (X := X)).app A ≫
          (toFlasqueEnvelope (X := X)).app B) ≫
        ((toFlasqueEnvelopeQuotient (X := X)).app B ≫
          (toFlasqueEnvelope (X := X)).app C) = 0 := by
      rw [Category.assoc, ← Category.assoc
        ((toFlasqueEnvelope (X := X)).app B)]
      rw [h, zero_comp, comp_zero]
    exact congrArg (fun k ↦ k.hom.app (op (⊤ : Opens X))) hs

/-- The homology of three consecutive envelope terms on global sections is
the cokernel of the preceding quotient map on global sections. -/
@[expose] noncomputable def flasqueEnvelopeSectionsHomologyIsoCokernel
    (A : Sheaf AddCommGrpCat X) :
    (flasqueEnvelopeSectionsShortComplex A).homology ≅
      cokernel (((toFlasqueEnvelopeQuotient (X := X)).app A).hom.app
        (op (⊤ : Opens X))) := by
  let B := (flasqueEnvelopeQuotientFunctor (X := X)).obj A
  let C := (flasqueEnvelopeQuotientFunctor (X := X)).obj B
  let S := flasqueEnvelopeSectionsShortComplex A
  let p : S.X₁ ⟶ B.obj.obj (op (⊤ : Opens X)) :=
    ((toFlasqueEnvelopeQuotient (X := X)).app A).hom.app
      (op (⊤ : Opens X))
  let i : B.obj.obj (op (⊤ : Opens X)) ⟶ S.X₂ :=
    ((toFlasqueEnvelope (X := X)).app B).hom.app
      (op (⊤ : Opens X))
  have hfi : p ≫ i = S.f := by
    rfl
  have hig : i ≫ S.g = 0 := by
    have h := congr_app
      (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) B
    change
      (toFlasqueEnvelope (X := X)).app B ≫
        (toFlasqueEnvelopeQuotient (X := X)).app B = 0 at h
    have hs :
        (toFlasqueEnvelope (X := X)).app B ≫
          ((toFlasqueEnvelopeQuotient (X := X)).app B ≫
            (toFlasqueEnvelope (X := X)).app C) = 0 := by
      rw [← Category.assoc, h, zero_comp]
    exact congrArg (fun k ↦ k.hom.app (op (⊤ : Opens X))) hs
  have hi : IsLimit (KernelFork.ofι i hig) := by
    let core : ShortComplex AddCommGrpCat :=
      { f := ((toFlasqueEnvelope (X := X)).app B).hom.app
          (op (⊤ : Opens X))
        g := ((toFlasqueEnvelopeQuotient (X := X)).app B).hom.app
          (op (⊤ : Opens X))
        zero := congrArg (fun k ↦ k.hom.app (op (⊤ : Opens X)))
          (congr_app
            (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) B) }
    have hcore : core.Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro x hx
      exact Sheaf.sections_exact_of_left_exact
        (flasqueEnvelopeShortExact B).exact
        (flasqueEnvelopeShortExact B).mono_f x hx
    let target : ShortComplex AddCommGrpCat := ShortComplex.mk i S.g hig
    let a : core ⟶ target :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := ((toFlasqueEnvelope (X := X)).app C).hom.app
          (op (⊤ : Opens X))
        comm₁₂ := by rfl
        comm₂₃ := by rfl }
    let _ : Epi a.τ₁ := by dsimp [a]; infer_instance
    let _ : IsIso a.τ₂ := by dsimp [a]; infer_instance
    let _ : Mono a.τ₃ := by dsimp [a]; infer_instance
    have htarget : target.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).1 hcore
    exact htarget.fIsKernel
  exact ShortComplex.homologyIsoCokernelOfKernelFactorization
    S (B.obj.obj (op (⊤ : Opens X))) p i hfi hig hi

/-- Evaluation of a sheaf on the terminal open, as an additive functor. -/
noncomputable abbrev terminalSectionsFunctor :
    Sheaf AddCommGrpCat X ⥤ AddCommGrpCat :=
  Sheaf.forget AddCommGrpCat X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op (⊤ : Opens X))

noncomputable instance : (terminalSectionsFunctor (X := X)).Additive := by
  constructor
  intro A B f g
  change
    ((Sheaf.forget AddCommGrpCat X).map (f + g)).app
        (op (⊤ : Opens X)) =
      ((Sheaf.forget AddCommGrpCat X).map f).app
          (op (⊤ : Opens X)) +
        ((Sheaf.forget AddCommGrpCat X).map g).app
          (op (⊤ : Opens X))
  rw [Functor.map_add]
  rfl

/-- The functorial flasque resolution after evaluation on the terminal open. -/
noncomputable abbrev flasqueResolutionSections
    (F : Sheaf AddCommGrpCat X) : CochainComplex AddCommGrpCat ℕ :=
  ((terminalSectionsFunctor (X := X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (flasqueResolution F)

/-- The three-term segment of the global-sections resolution agrees with the
arbitrary-sheaf envelope segment applied to the `n`th quotient iterate. -/
@[expose] noncomputable def flasqueResolutionSectionsScIso
    (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    (flasqueResolutionSections F).sc' n (n + 1) (n + 2) ≅
      flasqueEnvelopeSectionsShortComplex
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change
      𝟙 _ ≫ _ = _ ≫ 𝟙 _
    simp
    change _ = (terminalSectionsFunctor (X := X)).map
      ((flasqueResolution F).d n (n + 1))
    rw [flasqueResolution_d_succ]
    rfl
  · change
      𝟙 _ ≫ _ = _ ≫ 𝟙 _
    simp
    change _ = (terminalSectionsFunctor (X := X)).map
      ((flasqueResolution F).d (n + 1) (n + 2))
    rw [flasqueResolution_d_succ]
    rfl

/-- In degree `n + 1`, the homology of global sections of the functorial
flasque resolution is the cokernel of the degree-`n` envelope projection on
global sections. -/
@[expose] noncomputable def flasqueResolutionSectionsHomologyIsoCokernel
    (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    ((flasqueResolutionSections F).sc' n (n + 1) (n + 2)).homology ≅
      cokernel (((toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)).hom.app
          (op (⊤ : Opens X))) := by
  exact ShortComplex.homologyMapIso (flasqueResolutionSectionsScIso F n) ≪≫
    flasqueEnvelopeSectionsHomologyIsoCokernel
      ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)

/-- The actual degree-`n + 1` homology of global sections of the functorial
flasque resolution is the same cokernel. -/
@[expose] noncomputable def flasqueResolutionSectionsHomologyIsoCokernel'
    (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    (flasqueResolutionSections F).homology (n + 1) ≅
      cokernel (((toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)).hom.app
          (op (⊤ : Opens X))) :=
  (flasqueResolutionSections F).homologyIsoSc'
      n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    flasqueResolutionSectionsHomologyIsoCokernel F n

end TopCat.Sheaf

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- Positive-degree dimension shift through one functorial flasque envelope:
`H^(q+2)(A)` is `H^(q+1)(Q(A))`. -/
@[expose] noncomputable def flasqueEnvelopeDerivedSuccIso
    (A : Sheaf AddCommGrpCat X) (q : ℕ) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) ((q + 1) + 1)).obj A ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) (q + 1)).obj
          ((flasqueEnvelopeQuotientFunctor (X := X)).obj A) := by
  let S := flasqueEnvelopeShortComplex A
  let K := ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).obj ↧(ULift ℤ))
  let _ : TopCat.Sheaf.IsQuasiFlasque S.X₂ := by
    dsimp [S]
    infer_instance
  have hsub₁ : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (q + 1)) :=
    TopCat.Sheaf.IsQuasiFlasque.subsingleton_H_succ q S.X₂
  have hsub₂ : Subsingleton
      (CategoryTheory.Sheaf.H S.X₂ ((q + 1) + 1)) :=
    TopCat.Sheaf.IsQuasiFlasque.subsingleton_H_succ (q + 1) S.X₂
  exact ((@CategoryTheory.Abelian.Ext.covariantDimensionShift
    _ _ _ hExt S (flasqueEnvelopeShortExact A) K (q + 1) hsub₁ hsub₂).symm).toAddCommGrpIso

omit [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}] hExt in
/-- Applying `Q^n` after one application of `Q` agrees objectwise with the
chosen `Q^(n+1)` iterate. -/
theorem flasqueEnvelopeQuotientIterate_obj_obj (A : Sheaf AddCommGrpCat X) :
    ∀ n : ℕ,
      (flasqueEnvelopeQuotientIterate (X := X) n).obj
          ((flasqueEnvelopeQuotientFunctor (X := X)).obj A) =
        (flasqueEnvelopeQuotientIterate (X := X) (n + 1)).obj A
  | 0 => rfl
  | n + 1 => by
      change
        (flasqueEnvelopeQuotientFunctor (X := X)).obj
            ((flasqueEnvelopeQuotientIterate (X := X) n).obj
              ((flasqueEnvelopeQuotientFunctor (X := X)).obj A)) =
          (flasqueEnvelopeQuotientFunctor (X := X)).obj
            ((flasqueEnvelopeQuotientIterate (X := X) (n + 1)).obj A)
      rw [flasqueEnvelopeQuotientIterate_obj_obj A n]

/-- Iterating the positive-degree dimension shift identifies `H^(n+1)(A)`
with `H^1(Q^n(A))`. -/
@[expose] noncomputable def flasqueEnvelopeDerivedIterateIso
    (A : Sheaf AddCommGrpCat X) : (n : ℕ) →
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) (n + 1)).obj A ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj A)
  | 0 => Iso.refl _
  | n + 1 =>
      flasqueEnvelopeDerivedSuccIso A n ≪≫
        flasqueEnvelopeDerivedIterateIso
          ((flasqueEnvelopeQuotientFunctor (X := X)).obj A) n ≪≫
            (CategoryTheory.Sheaf.functorH
              (Opens.grothendieckTopology X) 1).mapIso
                (eqToIso (flasqueEnvelopeQuotientIterate_obj_obj A n))

/-- The first derived cohomology group is the cokernel of the degree-zero
cohomology map induced by the first envelope projection. -/
@[expose] noncomputable def flasqueEnvelopeDerivedOneIsoCokernelHZero
    (A : Sheaf AddCommGrpCat X) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 1).obj
        (flasqueEnvelopeShortComplex A).X₁ ≅
      cokernel ((CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 0).map
        (flasqueEnvelopeShortComplex A).g) := by
  let S := flasqueEnvelopeShortComplex A
  let K := ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).obj ↧(ULift ℤ))
  let _ : TopCat.Sheaf.IsQuasiFlasque S.X₂ := by
    dsimp [S]
    infer_instance
  have hsub : Subsingleton (CategoryTheory.Sheaf.H S.X₂ 1) :=
    TopCat.Sheaf.IsQuasiFlasque.subsingleton_H_succ 0 S.X₂
  exact (@CategoryTheory.Abelian.Ext.covariantCokernelIso
    _ _ _ hExt S (flasqueEnvelopeShortExact A) K hsub).symm

/-- Transport the degree-zero cokernel across the natural isomorphism between
degree-zero derived cohomology and terminal-open sections. -/
@[expose] noncomputable def flasqueEnvelopeCokernelHZeroIsoCokernelSections
    (A : Sheaf AddCommGrpCat X) :
    cokernel ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 0).map
        (flasqueEnvelopeShortComplex A).g) ≅
      cokernel ((terminalSectionsFunctor (X := X)).map
        (flasqueEnvelopeShortComplex A).g) := by
  let S := flasqueEnvelopeShortComplex A
  let e₀ := SheafCohomology.DegreeZero.functorHZeroIsoSections (X := X)
  have w :
      (CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology X) 0).map S.g ≫
        (e₀.app S.X₃).hom =
      (e₀.app S.X₂).hom ≫
        (terminalSectionsFunctor (X := X)).map S.g := by
    exact e₀.hom.naturality S.g
  exact cokernel.mapIso
    ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 0).map S.g)
    ((terminalSectionsFunctor (X := X)).map S.g)
      (e₀.app S.X₂) (e₀.app S.X₃) w

/-- The first derived cohomology group is the cokernel of the first envelope
projection after evaluation on the terminal open. -/
@[expose] noncomputable def flasqueEnvelopeDerivedOneIsoCokernelSections
    (A : Sheaf AddCommGrpCat X) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 1).obj
        (flasqueEnvelopeShortComplex A).X₁ ≅
      cokernel ((terminalSectionsFunctor (X := X)).map
        (flasqueEnvelopeShortComplex A).g) :=
  flasqueEnvelopeDerivedOneIsoCokernelHZero A ≪≫
    flasqueEnvelopeCokernelHZeroIsoCokernelSections A

/-- In degree one, derived sheaf cohomology agrees with the homology of
terminal-open sections of the functorial flasque resolution. -/
@[expose] noncomputable def derivedOneIsoFlasqueResolutionSectionsHomology
    (A : Sheaf AddCommGrpCat X) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 1).obj
        (flasqueEnvelopeShortComplex A).X₁ ≅
      (flasqueResolutionSections A).homology 1 :=
  flasqueEnvelopeDerivedOneIsoCokernelSections A ≪≫
    (flasqueResolutionSectionsHomologyIsoCokernel' A 0).symm

/-- In every positive degree, derived sheaf cohomology agrees with the homology
of terminal-open sections of the functorial flasque resolution. -/
@[expose] noncomputable def derivedSuccIsoFlasqueResolutionSectionsHomology
    (A : Sheaf AddCommGrpCat X) (n : ℕ) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) (n + 1)).obj A ≅
      (flasqueResolutionSections A).homology (n + 1) :=
  flasqueEnvelopeDerivedIterateIso A n ≪≫
    flasqueEnvelopeDerivedOneIsoCokernelSections
      ((flasqueEnvelopeQuotientIterate (X := X) n).obj A) ≪≫
        (flasqueResolutionSectionsHomologyIsoCokernel' A n).symm

omit [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}] hExt in
/-- A sheaf morphism induces the corresponding morphism between its first
functorial flasque-envelope short complexes. -/
@[expose] noncomputable def flasqueEnvelopeShortComplexMap
    {A B : Sheaf AddCommGrpCat X} (f : A ⟶ B) :
    flasqueEnvelopeShortComplex A ⟶ flasqueEnvelopeShortComplex B where
  τ₁ := f
  τ₂ := (flasqueEnvelopeFunctor (X := X)).map f
  τ₃ := (flasqueEnvelopeQuotientFunctor (X := X)).map f
  comm₁₂ := by simpa using (toFlasqueEnvelope (X := X)).naturality f
  comm₂₃ := (toFlasqueEnvelopeQuotient (X := X)).naturality f

/-- The positive-degree connecting isomorphism for the functorial envelope is
natural in the input sheaf. -/
@[expose] noncomputable def flasqueEnvelopeConnectingIso (q : ℕ) :
    flasqueEnvelopeQuotientFunctor (X := X) ⋙
        CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology X) (q + 1) ≅
      CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) ((q + 1) + 1) :=
  NatIso.ofComponents
    (fun A => (flasqueEnvelopeDerivedSuccIso A q).symm)
    (fun {A B} f => by
      ext x
      exact @CategoryTheory.Abelian.Ext.covariantDimensionShift_naturality
        _ _ _ hExt _ _ (flasqueEnvelopeShortExact A)
          (flasqueEnvelopeShortExact B) (flasqueEnvelopeShortComplexMap f)
            _ (q + 1) x)

end TopCat.Sheaf
