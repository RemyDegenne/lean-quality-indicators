/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import FiniteGroupTateCohomology.Norm

/-!
# Exceptional degrees in finite-group Tate cohomology

This module identifies Tate cohomology in degrees zero and minus one with the
cokernel and kernel of the norm from coinvariants to invariants, packages the
resulting exact sequence, and proves that the descriptions are natural in the
representation.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

private lemma tatePrevNegOne : (ComplexShape.up ℤ).prev (-1) = -2 := by simp

private lemma tateNextZero : (ComplexShape.up ℤ).next 0 = 1 := by simp

/-- The differential entering degree `-1` in the Tate complex, identified with
the concrete degree-zero group-homology differential. -/
@[expose]
noncomputable def tateDNegTwoArrowIso (M : Rep R G) :
    Arrow.mk ((tateComplex M).d (-2) (-1)) ≅ Arrow.mk (groupHomology.shortComplexH0 M).f :=
  Arrow.isoMk (groupHomology.chainsIso₁ M) (groupHomology.chainsIso₀ M) (by
    change (groupHomology.chainsIso₁ M).hom ≫ groupHomology.d₁₀ M =
      (groupHomology.inhomogeneousChains M).d 1 0 ≫
        (groupHomology.chainsIso₀ M).hom
    exact groupHomology.comp_d₁₀_eq M)

@[simp]
lemma tateDNegTwoArrowIso_hom_right (M : Rep R G) :
    (tateDNegTwoArrowIso M).hom.right = (groupHomology.chainsIso₀ M).hom := rfl

/-- The differential leaving degree `0` in the Tate complex, identified with
the concrete degree-zero group-cohomology differential. -/
@[expose]
noncomputable def tateDZeroArrowIso (M : Rep R G) :
    Arrow.mk ((tateComplex M).d 0 1) ≅ Arrow.mk (groupCohomology.shortComplexH0 M).g :=
  Arrow.isoMk (groupCohomology.cochainsIso₀ M) (groupCohomology.cochainsIso₁ M) (by
    change (groupCohomology.cochainsIso₀ M).hom ≫ groupCohomology.d₀₁ M =
      (groupCohomology.inhomogeneousCochains M).d 0 1 ≫
        (groupCohomology.cochainsIso₁ M).hom
    exact groupCohomology.comp_d₀₁_eq M)

@[simp]
lemma tateDZeroArrowIso_hom_left (M : Rep R G) :
    (tateDZeroArrowIso M).hom.left = (groupCohomology.cochainsIso₀ M).hom := rfl

/-- The opcycles in degree `-1` of the Tate complex are the coinvariants. -/
noncomputable def tateOpcyclesIsoNegOne (M : Rep R G) :
    (tateComplex M).opcycles (-1) ≅ (Rep.coinvariantsFunctor R G).obj M :=
  CokernelCofork.mapIsoOfIsColimit
    ((tateComplex M).opcyclesIsCokernel (-2) (-1) tatePrevNegOne)
    (groupHomology.shortComplexH0_exact M).gIsCokernel
    (tateDNegTwoArrowIso M)

/-- The cycles in degree `0` of the Tate complex are the invariants. -/
noncomputable def tateCyclesIsoZero (M : Rep R G) :
    (tateComplex M).cycles 0 ≅ (Rep.invariantsFunctor R G).obj M :=
  KernelFork.mapIsoOfIsLimit
    ((tateComplex M).cyclesIsKernel 0 1 tateNextZero)
    (groupCohomology.shortComplexH0_exact M).fIsKernel
    (tateDZeroArrowIso M)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma pOpcycles_tateOpcyclesIsoNegOne_hom (M : Rep R G) :
    (tateComplex M).pOpcycles (-1) ≫ (tateOpcyclesIsoNegOne M).hom =
      (tateDNegTwoArrowIso M).hom.right ≫ (groupHomology.shortComplexH0 M).g := by
  exact CokernelCofork.π_mapOfIsColimit (φ := (tateDNegTwoArrowIso M).hom) _ _

@[reassoc (attr := simp)]
lemma coinvariantsMk_tateOpcyclesIsoNegOne_inv (M : Rep R G) :
    (Rep.coinvariantsMk R G).app M ≫ (tateOpcyclesIsoNegOne M).inv =
      (groupHomology.chainsIso₀ M).inv ≫ (tateComplex M).pOpcycles (-1) :=
  (CommSq.vert_inv ⟨pOpcycles_tateOpcyclesIsoNegOne_hom M⟩).w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma tateCyclesIsoZero_hom_inclusion (M : Rep R G) :
    (tateCyclesIsoZero M).hom ≫ (groupCohomology.shortComplexH0 M).f =
      (tateComplex M).iCycles 0 ≫ (tateDZeroArrowIso M).hom.left := by
  dsimp [tateCyclesIsoZero]
  apply KernelFork.mapOfIsLimit_ι

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma tateOpcyclesIsoNegOne_naturality {M N : Rep R G} (f : M ⟶ N) :
    HomologicalComplex.opcyclesMap (tateComplex.map f) (-1) ≫
        (tateOpcyclesIsoNegOne N).hom =
      (tateOpcyclesIsoNegOne M).hom ≫ (Rep.coinvariantsFunctor R G).map f := by
  apply (cancel_epi ((tateComplex M).pOpcycles (-1))).1
  rw [← Category.assoc, HomologicalComplex.p_opcyclesMap]
  rw [pOpcycles_tateOpcyclesIsoNegOne_hom_assoc]
  rw [Category.assoc, pOpcycles_tateOpcyclesIsoNegOne_hom]
  change ((groupHomology.chainsMap (.id G) f).f 0 ≫
      (groupHomology.chainsIso₀ N).hom) ≫ (groupHomology.shortComplexH0 N).g = _
  rw [groupHomology.chainsMap_f_0_comp_chainsIso₀]
  change ((groupHomology.chainsIso₀ M).hom ≫
      (forget₂ (Rep R G) (ModuleCat R)).map f) ≫
      (Rep.coinvariantsMk R G).app N =
    ((groupHomology.chainsIso₀ M).hom ≫ (Rep.coinvariantsMk R G).app M) ≫
      (Rep.coinvariantsFunctor R G).map f
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (groupHomology.chainsIso₀ M).hom ≫ k)
    ((Rep.coinvariantsMk R G).naturality f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma tateCyclesIsoZero_naturality {M N : Rep R G} (f : M ⟶ N) :
    HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
        (tateCyclesIsoZero N).hom =
      (tateCyclesIsoZero M).hom ≫ (Rep.invariantsFunctor R G).map f := by
  let _ : Mono (ModuleCat.ofHom N.ρ.invariants.subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  apply (cancel_mono (ModuleCat.ofHom N.ρ.invariants.subtype)).1
  change HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
      ((tateCyclesIsoZero N).hom ≫ (groupCohomology.shortComplexH0 N).f) =
    (tateCyclesIsoZero M).hom ≫
      ((Rep.invariantsFunctor R G).map f ≫ ModuleCat.ofHom N.ρ.invariants.subtype)
  rw [tateCyclesIsoZero_hom_inclusion, invariantsMap_inclusion]
  change (HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
        (tateComplex N).iCycles 0) ≫ (groupCohomology.cochainsIso₀ N).hom =
    ((tateCyclesIsoZero M).hom ≫ (groupCohomology.shortComplexH0 M).f) ≫
      f.toModuleCatHom
  rw [tateCyclesIsoZero_hom_inclusion]
  rw [HomologicalComplex.cyclesMap_i]
  change (tateComplex M).iCycles 0 ≫
      ((groupCohomology.cochainsMap (.id G) f).f 0 ≫
        (groupCohomology.cochainsIso₀ N).hom) =
    (tateComplex M).iCycles 0 ≫
      ((groupCohomology.cochainsIso₀ M).hom ≫ f.toModuleCatHom)
  rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]

@[reassoc]
lemma tateCyclesIsoZero_inv_naturality {M N : Rep R G} (f : M ⟶ N) :
    (tateCyclesIsoZero M).inv ≫
        HomologicalComplex.cyclesMap (tateComplex.map f) 0 =
      (Rep.invariantsFunctor R G).map f ≫ (tateCyclesIsoZero N).inv :=
  (CommSq.vert_inv ⟨tateCyclesIsoZero_naturality f⟩).w.symm

/-- The natural norm, regarded as a functor to the arrow category. -/
@[expose]
noncomputable def normArrowFunctor : Rep R G ⥤ Arrow (ModuleCat R) where
  obj M := Arrow.mk (normFromCoinvariants M)
  map {M N} f := Arrow.homMk
    ((Rep.coinvariantsFunctor R G).map f)
    ((Rep.invariantsFunctor R G).map f)
    (normFromCoinvariants_naturality f).symm

/-- Kernels of the norm, functorially in the representation. -/
@[expose]
noncomputable def normKernelFunctor : Rep R G ⥤ ModuleCat R :=
  normArrowFunctor ⋙ Limits.ker (ModuleCat R)

/-- Cokernels of the norm, functorially in the representation. -/
@[expose]
noncomputable def normCokernelFunctor : Rep R G ⥤ ModuleCat R :=
  normArrowFunctor ⋙ Limits.coker (ModuleCat R)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma normKernelFunctor_map_ι {M N : Rep R G} (f : M ⟶ N) :
    (normKernelFunctor (R := R) (G := G)).map f ≫
        (Limits.ker.ι (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj N) =
      (Limits.ker.ι (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj M) ≫
        (Rep.coinvariantsFunctor R G).map f := by
  change (Limits.ker (ModuleCat R)).map
      ((normArrowFunctor (R := R) (G := G)).map f) ≫
        (Limits.ker.ι (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj N) =
    (Limits.ker.ι (ModuleCat R)).app
        ((normArrowFunctor (R := R) (G := G)).obj M) ≫
      Arrow.Hom.left ((normArrowFunctor (R := R) (G := G)).map f)
  exact (Limits.ker.ι (ModuleCat R)).naturality
    ((normArrowFunctor (R := R) (G := G)).map f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma normCokernelFunctor_π_map {M N : Rep R G} (f : M ⟶ N) :
    (Limits.coker.π (ModuleCat R)).app
        ((normArrowFunctor (R := R) (G := G)).obj M) ≫
        (normCokernelFunctor (R := R) (G := G)).map f =
      (Rep.invariantsFunctor R G).map f ≫
        (Limits.coker.π (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj N) := by
  change (Limits.coker.π (ModuleCat R)).app
      ((normArrowFunctor (R := R) (G := G)).obj M) ≫
        (Limits.coker (ModuleCat R)).map
          ((normArrowFunctor (R := R) (G := G)).map f) =
    Arrow.Hom.right ((normArrowFunctor (R := R) (G := G)).map f) ≫
      (Limits.coker.π (ModuleCat R)).app
        ((normArrowFunctor (R := R) (G := G)).obj N)
  exact ((Limits.coker.π (ModuleCat R)).naturality
    ((normArrowFunctor (R := R) (G := G)).map f)).symm

/-- The norm map appearing in the homology sequence of the Tate complex,
expressed between the concrete coinvariants and invariants. -/
noncomputable def tateNormFromCoinvariants (M : Rep R G) :
    (Rep.coinvariantsFunctor R G).obj M ⟶ (Rep.invariantsFunctor R G).obj M :=
  (tateOpcyclesIsoNegOne M).inv ≫
    (tateComplex M).opcyclesToCycles (-1) 0 ≫
    (tateCyclesIsoZero M).hom

set_option backward.isDefEq.respectTransparency false in
lemma tateNormFromCoinvariants_eq (M : Rep R G) :
    tateNormFromCoinvariants M = normFromCoinvariants M := by
  apply (cancel_epi ((Rep.coinvariantsMk R G).app M)).1
  apply (cancel_mono (groupCohomology.shortComplexH0 M).f).1
  simp [tateNormFromCoinvariants, Rep.tateNorm]
  simpa only [groupCohomology.shortComplexH0_f] using
    (coinvariantsMk_normFromCoinvariants_inclusion M).symm

/-- The four-term norm sequence in exceptional Tate degrees. -/
@[expose]
noncomputable def normSequence (M : Rep R G) : ComposableArrows (ModuleCat R) 3 :=
  ComposableArrows.mk₃
    ((tateComplex M).homologyι (-1) ≫ (tateOpcyclesIsoNegOne M).hom)
    (normFromCoinvariants M)
    ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma normSequence_first_naturality {M N : Rep R G} (f : M ⟶ N) :
    HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
        ((tateComplex N).homologyι (-1) ≫ (tateOpcyclesIsoNegOne N).hom) =
      ((tateComplex M).homologyι (-1) ≫ (tateOpcyclesIsoNegOne M).hom) ≫
        (Rep.coinvariantsFunctor R G).map f := by
  rw [← Category.assoc, HomologicalComplex.homologyι_naturality]
  rw [Category.assoc, tateOpcyclesIsoNegOne_naturality]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma normSequence_last_naturality {M N : Rep R G} (f : M ⟶ N) :
    ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
        HomologicalComplex.homologyMap (tateComplex.map f) 0 =
      (Rep.invariantsFunctor R G).map f ≫
        ((tateCyclesIsoZero N).inv ≫ (tateComplex N).homologyπ 0) := by
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, tateCyclesIsoZero_inv_naturality]
  rw [Category.assoc]

/-- The concrete norm sequence is isomorphic to the canonical homology sequence
of the Tate complex. -/
noncomputable def homologySequenceIsoNormSequence (M : Rep R G) :
    HomologicalComplex.HomologySequence.composableArrows₃ (tateComplex M) (-1) 0 ≅
      normSequence M :=
  ComposableArrows.isoMk₃ (Iso.refl _) (tateOpcyclesIsoNegOne M)
    (tateCyclesIsoZero M) (Iso.refl _)
    (by
      dsimp [-Fin.reduceFinMk, HomologicalComplex.HomologySequence.composableArrows₃,
        normSequence]
      simp)
    (by
      dsimp [-Fin.reduceFinMk, HomologicalComplex.HomologySequence.composableArrows₃,
        normSequence]
      rw [← tateNormFromCoinvariants_eq]
      simp [tateNormFromCoinvariants])
    (by
      dsimp [-Fin.reduceFinMk, HomologicalComplex.HomologySequence.composableArrows₃,
        normSequence]
      simp)

/-- The four-term norm sequence is exact. -/
lemma normSequence_exact (M : Rep R G) : (normSequence M).Exact :=
  ComposableArrows.exact_of_iso (homologySequenceIsoNormSequence M)
    (HomologicalComplex.HomologySequence.composableArrows₃_exact
      (tateComplex M) (-1) 0 (by simp))

set_option backward.defeqAttrib.useBackward true in
instance normSequence_mono_first (M : Rep R G) : Mono ((normSequence M).map' 0 1) := by
  dsimp [-Fin.reduceFinMk, normSequence]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance normSequence_epi_last (M : Rep R G) : Epi ((normSequence M).map' 2 3) := by
  dsimp [-Fin.reduceFinMk, normSequence]
  infer_instance

/-- Degree `-1` Tate cohomology is the kernel of the norm from coinvariants to
invariants. -/
noncomputable def tateCohomologyNegOneIsoKernelNorm (M : Rep R G) :
    tateCohomology M (-1) ≅ kernel (normFromCoinvariants M) :=
  IsLimit.conePointUniqueUpToIso ((normSequence_exact M).exact 0).fIsKernel
    (limit.isLimit (parallelPair (normFromCoinvariants M) 0))

/-- Degree `0` Tate cohomology is the cokernel of the norm from coinvariants to
invariants. -/
noncomputable def tateCohomologyZeroIsoCokernelNorm (M : Rep R G) :
    tateCohomology M 0 ≅ cokernel (normFromCoinvariants M) :=
  IsColimit.coconePointUniqueUpToIso ((normSequence_exact M).exact 1).gIsCokernel
    (colimit.isColimit (parallelPair (normFromCoinvariants M) 0))

@[reassoc]
lemma tateCohomologyNegOneIsoKernelNorm_hom_ι (M : Rep R G) :
    (tateCohomologyNegOneIsoKernelNorm M).hom ≫ kernel.ι (normFromCoinvariants M) =
      (tateComplex M).homologyι (-1) ≫ (tateOpcyclesIsoNegOne M).hom := by
  dsimp [tateCohomologyNegOneIsoKernelNorm]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    ((normSequence_exact M).exact 0).fIsKernel
    (limit.isLimit (parallelPair (normFromCoinvariants M) 0)) WalkingParallelPair.zero

@[reassoc]
lemma tateCohomologyZeroIsoCokernelNorm_π_hom (M : Rep R G) :
    ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
        (tateCohomologyZeroIsoCokernelNorm M).hom =
      cokernel.π (normFromCoinvariants M) := by
  dsimp [tateCohomologyZeroIsoCokernelNorm]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    ((normSequence_exact M).exact 1).gIsCokernel
    (colimit.isColimit (parallelPair (normFromCoinvariants M) 0)) WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
private lemma tateCohomologyNegOneIsoKernelNorm_hom_ι_functor (M : Rep R G) :
    (tateCohomologyNegOneIsoKernelNorm M).hom ≫
        (Limits.ker.ι (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj M) =
      (tateComplex M).homologyι (-1) ≫ (tateOpcyclesIsoNegOne M).hom :=
  tateCohomologyNegOneIsoKernelNorm_hom_ι M

set_option backward.isDefEq.respectTransparency false in
private lemma tateCohomologyZeroIsoCokernelNorm_π_hom_functor (M : Rep R G) :
    ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
        (tateCohomologyZeroIsoCokernelNorm M).hom =
      (Limits.coker.π (ModuleCat R)).app
        ((normArrowFunctor (R := R) (G := G)).obj M) :=
  tateCohomologyZeroIsoCokernelNorm_π_hom M

set_option backward.isDefEq.respectTransparency false in
/-- Degree `-1` Tate cohomology is naturally isomorphic to the kernel of the
norm from coinvariants to invariants. -/
noncomputable def tateCohomologyNegOneNatIsoKernelNorm :
    tateCohomologyFunctor (R := R) (G := G) (-1) ≅
      normKernelFunctor (R := R) (G := G) :=
  NatIso.ofComponents
    (fun M ↦ tateCohomologyNegOneIsoKernelNorm (R := R) (G := G) M) (by
    intro M N f
    change HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
        (tateCohomologyNegOneIsoKernelNorm N).hom =
      (tateCohomologyNegOneIsoKernelNorm M).hom ≫
        (normKernelFunctor (R := R) (G := G)).map f
    let _ : Mono ((Limits.ker.ι (ModuleCat R)).app
        ((normArrowFunctor (R := R) (G := G)).obj N)) := by
      dsimp [Limits.ker.ι, normArrowFunctor]
      infer_instance
    apply (cancel_mono ((Limits.ker.ι (ModuleCat R)).app
      ((normArrowFunctor (R := R) (G := G)).obj N))).1
    calc
      (HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
          (tateCohomologyNegOneIsoKernelNorm N).hom) ≫
          (Limits.ker.ι (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj N) =
        HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
          ((tateCohomologyNegOneIsoKernelNorm N).hom ≫
            (Limits.ker.ι (ModuleCat R)).app
              ((normArrowFunctor (R := R) (G := G)).obj N)) := Category.assoc _ _ _
      _ = HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
          ((tateComplex N).homologyι (-1) ≫
            (tateOpcyclesIsoNegOne N).hom) := by
              rw [tateCohomologyNegOneIsoKernelNorm_hom_ι_functor]
      _ = ((tateComplex M).homologyι (-1) ≫
          (tateOpcyclesIsoNegOne M).hom) ≫
          (Rep.coinvariantsFunctor R G).map f := normSequence_first_naturality f
      _ = ((tateCohomologyNegOneIsoKernelNorm M).hom ≫
          (Limits.ker.ι (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj M)) ≫
          (Rep.coinvariantsFunctor R G).map f := by
              rw [tateCohomologyNegOneIsoKernelNorm_hom_ι_functor]
      _ = (tateCohomologyNegOneIsoKernelNorm M).hom ≫
          ((Limits.ker.ι (ModuleCat R)).app
              ((normArrowFunctor (R := R) (G := G)).obj M) ≫
            (Rep.coinvariantsFunctor R G).map f) := Category.assoc _ _ _
      _ = (tateCohomologyNegOneIsoKernelNorm M).hom ≫
          ((normKernelFunctor (R := R) (G := G)).map f ≫
            (Limits.ker.ι (ModuleCat R)).app
              ((normArrowFunctor (R := R) (G := G)).obj N)) := by
                rw [normKernelFunctor_map_ι]
      _ = ((tateCohomologyNegOneIsoKernelNorm M).hom ≫
          (normKernelFunctor (R := R) (G := G)).map f) ≫
          (Limits.ker.ι (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj N) :=
              (Category.assoc _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Degree `0` Tate cohomology is naturally isomorphic to the cokernel of the
norm from coinvariants to invariants. -/
noncomputable def tateCohomologyZeroNatIsoCokernelNorm :
    tateCohomologyFunctor (R := R) (G := G) 0 ≅
      normCokernelFunctor (R := R) (G := G) :=
  NatIso.ofComponents
    (fun M ↦ tateCohomologyZeroIsoCokernelNorm (R := R) (G := G) M) (by
    intro M N f
    change HomologicalComplex.homologyMap (tateComplex.map f) 0 ≫
        (tateCohomologyZeroIsoCokernelNorm N).hom =
      (tateCohomologyZeroIsoCokernelNorm M).hom ≫
        (normCokernelFunctor (R := R) (G := G)).map f
    apply (cancel_epi
      ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0)).1
    calc
      ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          (HomologicalComplex.homologyMap (tateComplex.map f) 0 ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom) =
        (((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          HomologicalComplex.homologyMap (tateComplex.map f) 0) ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom :=
              (Category.assoc _ _ _).symm
      _ = ((Rep.invariantsFunctor R G).map f ≫
          ((tateCyclesIsoZero N).inv ≫ (tateComplex N).homologyπ 0)) ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom := by
              rw [normSequence_last_naturality]
      _ = (Rep.invariantsFunctor R G).map f ≫
          (((tateCyclesIsoZero N).inv ≫ (tateComplex N).homologyπ 0) ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom) := Category.assoc _ _ _
      _ = (Rep.invariantsFunctor R G).map f ≫
          (Limits.coker.π (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj N) := by
              rw [tateCohomologyZeroIsoCokernelNorm_π_hom_functor]
      _ = (Limits.coker.π (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj M) ≫
          (normCokernelFunctor (R := R) (G := G)).map f := by
            rw [normCokernelFunctor_π_map]
      _ = (((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          (tateCohomologyZeroIsoCokernelNorm M).hom) ≫
            (normCokernelFunctor (R := R) (G := G)).map f := by
              rw [tateCohomologyZeroIsoCokernelNorm_π_hom_functor]
      _ = ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          ((tateCohomologyZeroIsoCokernelNorm M).hom ≫
            (normCokernelFunctor (R := R) (G := G)).map f) :=
              Category.assoc _ _ _)

/-- The degree `-1` natural isomorphism has the kernel comparison as its component. -/
lemma tateCohomologyNegOneNatIsoKernelNorm_hom_app (M : Rep R G) :
    (tateCohomologyNegOneNatIsoKernelNorm (R := R) (G := G)).hom.app M =
      (tateCohomologyNegOneIsoKernelNorm M).hom := by
  rfl

/-- The degree `0` natural isomorphism has the cokernel comparison as its component. -/
lemma tateCohomologyZeroNatIsoCokernelNorm_hom_app (M : Rep R G) :
    (tateCohomologyZeroNatIsoCokernelNorm (R := R) (G := G)).hom.app M =
      (tateCohomologyZeroIsoCokernelNorm M).hom := by
  rfl

end FiniteGroupTateCohomology
