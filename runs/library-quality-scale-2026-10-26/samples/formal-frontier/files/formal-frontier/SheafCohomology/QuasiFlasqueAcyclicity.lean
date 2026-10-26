/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.QuasiFlasqueExactness
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

public section

/-!
# Cohomological acyclicity of quasi-flasque sheaves

This file constructs a flasque injective envelope of an abelian sheaf as the
product of injective skyscraper sheaves over all points.  Its quotient remains
quasi-flasque, so the global-sections exactness theorem and the covariant long
exact `Ext` sequence give vanishing of positive-degree sheaf cohomology by
dimension shifting.

The space, coefficient category, and product index live in a common universe.
The accepted compact-open exactness interface couples these universes; this
file does not provide a wrapper for independently varying universes.

## Main results

* `TopCat.Sheaf.IsFlasque.product`: a product of flasque abelian sheaves is
  flasque.
* `TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelopeShortExact`: the
  skyscraper-product envelope gives a short exact sequence.
* `TopCat.Sheaf.IsQuasiFlasque.subsingleton_H_succ`: positive-degree
  cohomology of a quasi-flasque sheaf vanishes on a compact prespectral
  quasi-separated space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopCat

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

private lemma piMap_epi {ι : Type u} {A B : ι → AddCommGrpCat.{u}}
    [HasProduct A] [HasProduct B] (f : ∀ i, A i ⟶ B i)
    [∀ i, Epi (f i)] : Epi (Limits.Pi.map f) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  choose x hx using fun i =>
    (AddCommGrpCat.epi_iff_surjective (f i)).mp (inferInstance : Epi (f i))
      (Concrete.productEquiv B y i)
  refine ⟨(Concrete.productEquiv A).symm x, ?_⟩
  apply (Concrete.productEquiv B).injective
  funext i
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
    ← ConcreteCategory.comp_apply, Limits.Pi.map_π, ConcreteCategory.comp_apply,
    Concrete.productEquiv_symm_apply_π]
  simpa only [Concrete.productEquiv_apply_apply] using hx i

namespace IsFlasque

set_option backward.isDefEq.respectTransparency false in
/-- A product of flasque `AddCommGrpCat`-valued sheaves is flasque. -/
noncomputable instance product {ι : Type u}
    (G : ι → Sheaf AddCommGrpCat.{u} X) [HasProduct G]
    [∀ i, TopCat.Sheaf.IsFlasque (G i)] :
    TopCat.Sheaf.IsFlasque (∏ᶜ G) where
  epi {U V} r := by
    let ev (W : (Opens X)ᵒᵖ) : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
      Sheaf.forget AddCommGrpCat.{u} X ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj W
    let hForgetPreserves : PreservesLimit (Discrete.functor G)
        (Sheaf.forget AddCommGrpCat.{u} X) := inferInstance
    let hHasLimits : HasLimitsOfShape (Discrete ι) AddCommGrpCat.{u} := inferInstance
    let hEvalUPreserves : PreservesLimitsOfShape (Discrete ι)
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U) := inferInstance
    let hEvalVPreserves : PreservesLimitsOfShape (Discrete ι)
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V) := inferInstance
    let hUnderlyingUPreserves : PreservesLimit
        (Discrete.functor G ⋙ Sheaf.forget AddCommGrpCat.{u} X)
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U) :=
      evaluation_preservesLimit _ U
    let hUnderlyingVPreserves : PreservesLimit
        (Discrete.functor G ⋙ Sheaf.forget AddCommGrpCat.{u} X)
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V) :=
      evaluation_preservesLimit _ V
    let hEvUPreserves : PreservesLimit (Discrete.functor G) (ev U) := inferInstance
    let hEvVPreserves : PreservesLimit (Discrete.functor G) (ev V) := inferInstance
    let eU : (ev U).obj (∏ᶜ G) ≅ ∏ᶜ fun i => (ev U).obj (G i) :=
      PreservesProduct.iso (ev U) G
    let eV : (ev V).obj (∏ᶜ G) ≅ ∏ᶜ fun i => (ev V).obj (G i) :=
      PreservesProduct.iso (ev V) G
    have eUHom : IsIso eU.hom := eU.isIso_hom
    have eVHom : IsIso eV.hom := eV.isIso_hom
    let eUEpi : Epi eU.hom := by infer_instance
    have piEpi : Epi (Limits.Pi.map fun i => (G i).obj.map r) := piMap_epi _
    have h :
        (∏ᶜ G).obj.map r ≫ eV.hom =
          eU.hom ≫ Limits.Pi.map (fun i => (G i).obj.map r) := by
      apply Pi.hom_ext
      intro i
      have eUπ :
          eU.hom ≫ Pi.π (fun i => (ev U).obj (G i)) i =
            (ev U).map (Pi.π G i) := by
        dsimp [eU]
        rw [piComparison_comp_π]
      have eVπ :
          eV.hom ≫ Pi.π (fun i => (ev V).obj (G i)) i =
            (ev V).map (Pi.π G i) := by
        dsimp [eV]
        rw [piComparison_comp_π]
      erw [Category.assoc, eVπ]
      erw [Category.assoc, Limits.Pi.map_π]
      erw [← Category.assoc, eUπ]
      exact (Pi.π G i).hom.naturality r
    have hCompositeEpi : Epi ((∏ᶜ G).obj.map r ≫ eV.hom) := by
      rw [h]
      exact CategoryTheory.epi_comp' eUEpi piEpi
    exact epi_comp_iff_of_isIso ((∏ᶜ G).obj.map r) eV.hom |>.mp inferInstance

end IsFlasque

namespace IsQuasiFlasque

variable (F : Sheaf AddCommGrpCat.{u} X)

/-- The stalk of `F` at `x`, used in the skyscraper-product envelope. -/
abbrev stalkObject (x : X) : AddCommGrpCat.{u} :=
  (Sheaf.forget AddCommGrpCat.{u} X ⋙
    Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F

/-- A chosen injective object containing the stalk of `F` at `x`. -/
abbrev stalkInjective (x : X) : AddCommGrpCat.{u} :=
  Injective.under (stalkObject F x)

/-- The skyscraper sheaf associated to the chosen injective envelope of `Fₓ`. -/
abbrev stalkInjectiveSkyscraper (x : X) : Sheaf AddCommGrpCat.{u} X :=
  (skyscraperSheafFunctor x).obj (stalkInjective F x)

noncomputable instance (x : X) : Injective (stalkInjectiveSkyscraper F x) :=
  Injective.injective_of_adjoint (stalkSkyscraperSheafAdjunction x) _

noncomputable instance (x : X) : TopCat.Sheaf.IsFlasque
    (stalkInjectiveSkyscraper F x) := by
  dsimp [stalkInjectiveSkyscraper]
  exact isFlasque_skyscraperSheaf_of_hasZeroObject x _

/-- The adjunction unit followed by the chosen injective stalk embedding. -/
@[expose] noncomputable def toStalkInjectiveSkyscraper (x : X) :
    F ⟶ stalkInjectiveSkyscraper F x :=
  (stalkSkyscraperSheafAdjunction x).homEquiv F (stalkInjective F x)
    (Injective.ι (stalkObject F x))

noncomputable instance toStalkInjectiveSkyscraper_stalk_mono (x : X) :
    Mono ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toStalkInjectiveSkyscraper F x).hom) := by
  change Mono ((Sheaf.forget AddCommGrpCat.{u} X ⋙
    Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toStalkInjectiveSkyscraper F x))
  have h :
      (Sheaf.forget AddCommGrpCat.{u} X ⋙
          Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toStalkInjectiveSkyscraper F x) ≫
        (stalkSkyscraperSheafAdjunction x).counit.app (stalkInjective F x) =
      Injective.ι (stalkObject F x) := by
    calc
      _ = ((stalkSkyscraperSheafAdjunction x).homEquiv F
          (stalkInjective F x)).symm (toStalkInjectiveSkyscraper F x) :=
        ((stalkSkyscraperSheafAdjunction x).homEquiv_counit F
          (stalkInjective F x) (toStalkInjectiveSkyscraper F x)).symm
      _ = _ := ((stalkSkyscraperSheafAdjunction x).homEquiv F
        (stalkInjective F x)).symm_apply_apply (Injective.ι (stalkObject F x))
  let hInjectiveMono : Mono (Injective.ι (stalkObject F x)) := Injective.ι_mono _
  exact mono_of_mono_fac h

/-- The product, over all points, of the injective skyscraper envelopes of the stalks. -/
abbrev flasqueInjectiveEnvelope : Sheaf AddCommGrpCat.{u} X :=
  ∏ᶜ fun x : X => stalkInjectiveSkyscraper F x

/-- The canonical map from `F` to its skyscraper-product injective envelope. -/
@[expose] noncomputable def toFlasqueInjectiveEnvelope :
    F ⟶ flasqueInjectiveEnvelope F :=
  Pi.lift fun x => toStalkInjectiveSkyscraper F x

noncomputable instance toFlasqueInjectiveEnvelope_mono :
    Mono (toFlasqueInjectiveEnvelope F) := by
  let hStalkMono (x : X) :
      Mono ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toFlasqueInjectiveEnvelope F).hom) := by
    change Mono ((Sheaf.forget AddCommGrpCat.{u} X ⋙
      Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toFlasqueInjectiveEnvelope F))
    let hComponentMono : Mono ((Sheaf.forget AddCommGrpCat.{u} X ⋙
        Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toStalkInjectiveSkyscraper F x)) := by
      change Mono ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toStalkInjectiveSkyscraper F x).hom)
      infer_instance
    have h :
        (Sheaf.forget AddCommGrpCat.{u} X ⋙
            Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (toFlasqueInjectiveEnvelope F) ≫
          (Sheaf.forget AddCommGrpCat.{u} X ⋙
            Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (Pi.π (fun y : X => stalkInjectiveSkyscraper F y) x) =
        (Sheaf.forget AddCommGrpCat.{u} X ⋙
          Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toStalkInjectiveSkyscraper F x) := by
      rw [← (Sheaf.forget AddCommGrpCat.{u} X ⋙
        Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp]
      simp [toFlasqueInjectiveEnvelope]
      rfl
    exact mono_of_mono_fac h
  exact TopCat.Presheaf.mono_of_stalk_mono _

noncomputable instance flasqueInjectiveEnvelope_injective :
    Injective (flasqueInjectiveEnvelope F) := by
  dsimp [flasqueInjectiveEnvelope]
  infer_instance

noncomputable instance : TopCat.Sheaf.IsFlasque (flasqueInjectiveEnvelope F) := by
  dsimp [flasqueInjectiveEnvelope]
  infer_instance

/-- The cokernel of the canonical map to the flasque injective envelope. -/
abbrev flasqueInjectiveQuotient : Sheaf AddCommGrpCat.{u} X :=
  cokernel (toFlasqueInjectiveEnvelope F)

/-- The canonical kernel-envelope-quotient short complex. -/
abbrev flasqueInjectiveEnvelopeShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (toFlasqueInjectiveEnvelope F)
    (cokernel.π (toFlasqueInjectiveEnvelope F))
    (cokernel.condition (toFlasqueInjectiveEnvelope F))

/-- The canonical kernel-envelope-quotient short complex is short exact. -/
theorem flasqueInjectiveEnvelopeShortExact :
    (flasqueInjectiveEnvelopeShortComplex F).ShortExact where
  exact := ShortComplex.exact_cokernel (toFlasqueInjectiveEnvelope F)

noncomputable instance [QuasiSeparatedSpace X] [PrespectralSpace X]
    [TopCat.Sheaf.IsQuasiFlasque F] :
    TopCat.Sheaf.IsQuasiFlasque (flasqueInjectiveQuotient F) := by
  exact TopCat.Sheaf.IsQuasiFlasque.of_shortExact_of_isQuasiFlasque₁₂
    (S := flasqueInjectiveEnvelopeShortComplex F)
    (flasqueInjectiveEnvelopeShortExact F)

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-flasque abelian sheaf on a compact prespectral quasi-separated
space has trivial cohomology in every positive degree. -/
theorem subsingleton_H_succ [CompactSpace X] [QuasiSeparatedSpace X]
    [PrespectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [hExt : HasExt.{u} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (q : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsQuasiFlasque G] :
    Subsingleton (CategoryTheory.Sheaf.H.{u} G (q + 1)) := by
  induction q generalizing G with
  | zero =>
      let hAbelian : Abelian (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
        inferInstance
      let hGroup : AddCommGroup (CategoryTheory.Sheaf.H.{u} G 1) :=
        @Abelian.Ext.instAddCommGroup
          (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (inferInstance : Category (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          hAbelian hExt
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            ↧(ULift ℤ)) G 1
      refine subsingleton_of_forall_eq 0 fun x => ?_
      let S := flasqueInjectiveEnvelopeShortComplex G
      have hS : S.ShortExact := flasqueInjectiveEnvelopeShortExact G
      let hInjective : Injective S.X₂ := by
        change Injective (flasqueInjectiveEnvelope G)
        exact flasqueInjectiveEnvelope_injective G
      have hxI := @Abelian.Ext.eq_zero_of_injective
        (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (inferInstance : Category (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
        hAbelian hExt _ S.X₂ 0 hInjective
        (x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1))
      obtain ⟨xQ, hxQ⟩ :=
        @Abelian.Ext.covariant_sequence_exact₁
          (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (inferInstance : Category (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          hAbelian hExt
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            ↧(ULift ℤ)) S hS 1 x hxI 0 rfl
      have hSectionsEpi : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
        TopCat.Sheaf.IsQuasiFlasque.epi_of_shortExact hS
      obtain ⟨sI, hsI⟩ :=
        (AddCommGrpCat.epi_iff_surjective (S.g.hom.app (op (⊤ : Opens X)))).mp
          inferInstance
          (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop xQ)
      let hGroupI : AddCommGroup (CategoryTheory.Sheaf.H.{u} S.X₂ 0) :=
        @Abelian.Ext.instAddCommGroup
          (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (inferInstance : Category (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          hAbelian hExt
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            ↧(ULift ℤ)) S.X₂ 0
      let hGroupQ : AddCommGroup (CategoryTheory.Sheaf.H.{u} S.X₃ 0) :=
        @Abelian.Ext.instAddCommGroup
          (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (inferInstance : Category (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          hAbelian hExt
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            ↧(ULift ℤ)) S.X₃ 0
      let xI : CategoryTheory.Sheaf.H.{u} S.X₂ 0 :=
        (CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm sI
      have hxQI : CategoryTheory.Sheaf.H.map S.g 0 xI = xQ := by
        apply (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).injective
        calc
          CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop
              (CategoryTheory.Sheaf.H.map S.g 0 xI) =
              S.g.hom.app (op (⊤ : Opens X))
                (CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop xI) :=
            (CategoryTheory.Sheaf.H.equiv₀_naturality
              isTerminalTop S.g xI).symm
          _ = S.g.hom.app (op (⊤ : Opens X)) sI := by
            simp [xI]
          _ = CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop xQ := hsI
      rw [← hxQ, ← hxQI]
      dsimp only [CategoryTheory.Sheaf.H.map, Abelian.Ext.postcomp,
        AddMonoidHom.flip_apply]
      have hcomp := @ShortComplex.ShortExact.comp_extClass
        (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (inferInstance : Category (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
        hAbelian hExt S hS
      erw [Abelian.Ext.bilinearComp_apply_apply,
        Abelian.Ext.comp_assoc_of_second_deg_zero, hcomp]
      exact Abelian.Ext.comp_zero _ _ _ _ _
  | succ q ih =>
      let hAbelian : Abelian (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
        inferInstance
      let hGroup : AddCommGroup (CategoryTheory.Sheaf.H.{u} G (q + 2)) :=
        @Abelian.Ext.instAddCommGroup
          (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (inferInstance : Category (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          hAbelian hExt
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            ↧(ULift ℤ)) G (q + 2)
      refine subsingleton_of_forall_eq 0 fun x => ?_
      let S := flasqueInjectiveEnvelopeShortComplex G
      have hS : S.ShortExact := flasqueInjectiveEnvelopeShortExact G
      let hInjective : Injective S.X₂ := by
        change Injective (flasqueInjectiveEnvelope G)
        exact flasqueInjectiveEnvelope_injective G
      have hxI := @Abelian.Ext.eq_zero_of_injective
        (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (inferInstance : Category (CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
        hAbelian hExt _ S.X₂ (q + 1) hInjective
        (x.comp (Abelian.Ext.mk₀ S.f) (add_zero (q + 2)))
      obtain ⟨xQ, hxQ⟩ :=
        @Abelian.Ext.covariant_sequence_exact₁
          (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (inferInstance : Category (CategoryTheory.Sheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          hAbelian hExt
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            ↧(ULift ℤ)) S hS (q + 2) x hxI (q + 1) rfl
      let hQuasiFlasqueQ : TopCat.Sheaf.IsQuasiFlasque S.X₃ := inferInstance
      let hSubsingletonQ : Subsingleton
          (CategoryTheory.Sheaf.H.{u} S.X₃ (q + 1)) := ih S.X₃
      have hxQ0 : xQ = 0 := Subsingleton.elim _ _
      rw [← hxQ, hxQ0]
      exact Abelian.Ext.zero_comp _ _ _ _ _

end IsQuasiFlasque

end TopCat.Sheaf
