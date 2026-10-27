/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.CoefficientRingBase
public import ProjectiveSpace.StandardChartScheme
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Sets.OpenCover

/-!
# Geometric integrality of finite-dimensional projective space

The coefficient morphism of a finite-dimensional projective space is
geometrically integral over every commutative ring. The finite-coordinate-index
form uses a finite nonempty coordinate type; the dimension-indexed form uses
`Fin (n + 1)`.

The finite-coordinate restriction comes from the available polynomial
presentation of the standard charts, not from geometric integrality itself.
Nonemptiness is necessary: with no homogeneous coordinates, projective space
over a field is empty and is not integral.

The geometric-property interface and the affine-space base-change approach are
provided by Mathlib's algebraic geometry library, particularly the work of
Andrew Yang.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

private theorem standardChartPolynomial_isPullback
    (R K : Type (max u v)) [CommRing R] [CommRing K]
    (σ : Type v) (i : σ) (φ : R →+* K) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (σ := {j : σ // j ≠ i}) φ)))
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial {j : σ // j ≠ i} K)))
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial {j : σ // j ≠ i} R)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  -- Affine space requires its coordinate type in the scheme's universe.
  let I : Type (max u v) := ULift.{max u v} {j : σ // j ≠ i}
  let e : {j : σ // j ≠ i} ≃ I := Equiv.ulift.symm
  have hLift : IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := I) φ)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial I K)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial I R)))
      (Spec.map (CommRingCat.ofHom φ)) := by
    refine (AffineSpace.isPullback_map (n := I)
      (Spec.map (CommRingCat.ofHom φ))).of_iso
        (AffineSpace.SpecIso I (CommRingCat.of K))
        (AffineSpace.SpecIso I (CommRingCat.of R))
        (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [AffineSpace.map_SpecMap, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    · simp only [Iso.refl_hom, Category.comp_id]
      rw [← Iso.inv_comp_eq]
      exact AffineSpace.SpecIso_inv_over (CommRingCat.of K)
    · simp only [Iso.refl_hom, Category.comp_id]
      rw [← Iso.inv_comp_eq]
      exact AffineSpace.SpecIso_inv_over (CommRingCat.of R)
    · simp
  let eR : Spec (CommRingCat.of (MvPolynomial I R)) ≅
      Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} R)) :=
    Scheme.Spec.mapIso (MvPolynomial.renameEquiv R e).toRingEquiv.toCommRingCatIso.op
  let eK : Spec (CommRingCat.of (MvPolynomial I K)) ≅
      Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} K)) :=
    Scheme.Spec.mapIso (MvPolynomial.renameEquiv K e).toRingEquiv.toCommRingCatIso.op
  refine hLift.of_iso eK eR (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := I) φ)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := R) e).toRingHom) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.map (σ := {j : σ // j ≠ i}) φ))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (MvPolynomial.map_comp_rename φ e)
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial I K)) ≫
        𝟙 _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial {j : σ // j ≠ i} K))
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (MvPolynomial.rename_C e r).symm
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial I R)) ≫
        𝟙 _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := R) e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : R →+* MvPolynomial {j : σ // j ≠ i} R))
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (MvPolynomial.rename_C e r).symm
  · simp

private theorem standardCoordinateChart_isPullback
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Fintype σ] (i : σ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (σ := {j : σ // j ≠ i}) (algebraMap R K))))
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial {j : σ // j ≠ i} K)))
      (standardCoordinateChartMap R σ i ≫ polynomialProjToSpec R σ)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  rw [standardCoordinateChartMap_toSpec]
  exact standardChartPolynomial_isPullback R K σ i (algebraMap R K)

private def standardCoordinateChartPullbackIso
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Fintype σ] (i : σ) :
    pullback (standardCoordinateChartMap R σ i ≫ polynomialProjToSpec R σ)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} K)) :=
  (standardCoordinateChart_isPullback R K σ i).isoPullback.symm

private theorem standardCoordinateChartPullbackIso_inv_fst
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Fintype σ] (i : σ) :
    (standardCoordinateChartPullbackIso R K σ i).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (σ := {j : σ // j ≠ i}) (algebraMap R K))) :=
  (standardCoordinateChart_isPullback R K σ i).isoPullback_hom_fst

private theorem standardCoordinateChartPullbackIso_inv_snd
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Fintype σ] (i : σ) :
    (standardCoordinateChartPullbackIso R K σ i).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial {j : σ // j ≠ i} K)) :=
  (standardCoordinateChart_isPullback R K σ i).isoPullback_hom_snd

private def allOnesEvaluation
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) : MvPolynomial σ R →+* Γ(Spec (CommRingCat.of K), ⊤) :=
  MvPolynomial.eval₂Hom
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp (algebraMap R K)) (fun _ ↦ 1)

private theorem allOnesEvaluation_map_irrelevant
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Nonempty σ] :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).toIdeal.map
      (allOnesEvaluation R K σ) = ⊤ := by
  classical
  apply (Ideal.eq_top_iff_one _).mpr
  let i : σ := Classical.choice inferInstance
  have hXi : MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule σ R 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X R i)
  have hx := HomogeneousIdeal.mem_irrelevant_of_mem
    (MvPolynomial.homogeneousSubmodule σ R) (by simp : 0 < (1 : ℕ)) hXi
  have hEval : allOnesEvaluation R K σ (MvPolynomial.X i) = 1 :=
    MvPolynomial.eval₂Hom_X' _ _ i
  exact hEval ▸ Ideal.mem_map_of_mem (allOnesEvaluation R K σ) hx

private def allOnesProjPoint
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Nonempty σ] :
    Spec (CommRingCat.of K) ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) :=
  Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule σ R)
    (allOnesEvaluation R K σ) (allOnesEvaluation_map_irrelevant R K σ)

private theorem allOnesProjPoint_toSpec
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Nonempty σ] :
    allOnesProjPoint R K σ ≫ polynomialProjToSpec R σ =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  have hcoeff :
      (mvPolynomialDegreeZeroEquiv R σ).toRingEquiv.toCommRingCatIso.hom ≫
          CommRingCat.ofHom ((allOnesEvaluation R K σ).comp
            (algebraMap (MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R))) =
        CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    ext r
    change allOnesEvaluation R K σ (MvPolynomial.C r) = _
    exact MvPolynomial.eval₂Hom_C _ _ _
  rw [polynomialProjToSpec_eq_toSpecZero, ← Category.assoc, allOnesProjPoint,
    Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp, hcoeff,
    Spec.map_comp, ← Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

private theorem allOnesProjPoint_preimage_basicOpen
    (R K : Type (max u v)) [CommRing R] [CommRing K] [Algebra R K]
    (σ : Type v) [Nonempty σ] (i : σ) :
    allOnesProjPoint R K σ ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) = ⊤ := by
  have hXi : MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule σ R 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X R i)
  rw [allOnesProjPoint, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ (by simp) hXi]
  simp [allOnesEvaluation, Scheme.basicOpen_one]

private theorem pullbackOpenCoverOfLeft_fst
    {X Y S : Scheme.{u}} (C : Scheme.OpenCover.{v} X)
    (f : X ⟶ S) (g : Y ⟶ S) (i : C.I₀) :
    (Scheme.Pullback.openCoverOfLeft C f g).f i ≫ pullback.fst f g =
      pullback.fst (C.f i ≫ f) g ≫ C.f i := by
  change pullback.lift _ _ _ ≫ pullback.fst f g = _
  exact pullback.lift_fst _ _ _

private theorem pullbackOpenCoverOfLeft_snd
    {X Y S : Scheme.{u}} (C : Scheme.OpenCover.{v} X)
    (f : X ⟶ S) (g : Y ⟶ S) (i : C.I₀) :
    (Scheme.Pullback.openCoverOfLeft C f g).f i ≫ pullback.snd f g =
      pullback.snd (C.f i ≫ f) g := by
  change pullback.lift _ _ _ ≫ pullback.snd f g = _
  exact (pullback.lift_snd (f := f) (g := g)
    (pullback.fst (C.f i ≫ f) g ≫ C.f i)
    (pullback.snd (C.f i ≫ f) g ≫ 𝟙 Y)
    (by simp only [Category.assoc, Category.comp_id,
      pullback.condition])).trans (Category.comp_id _)

private theorem isIntegral_standardCoordinatePullback
    (R K : Type (max u v)) [CommRing R] [Field K] [Algebra R K]
    (σ : Type v) [Finite σ] [Nonempty σ] :
    IsIntegral (pullback (polynomialProjToSpec R σ)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  classical
  let _ := Fintype.ofFinite σ
  let p := polynomialProjToSpec R σ
  let y := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let T := pullback p y
  let C : T.OpenCover := Scheme.Pullback.openCoverOfLeft
    (standardCoordinateAffineOpenCover R σ).openCover p y
  have : ∀ i : σ, IsOpenImmersion (C.f i) := fun i ↦ C.map_prop i
  have hIntegral : ∀ i : σ, IsIntegral (C.X i) := fun i ↦ by
    change IsIntegral (pullback (standardCoordinateChartMap R σ i ≫ p) y)
    exact IsIntegral.of_isIso (standardCoordinateChartPullbackIso R K σ i).inv
  have : ∀ i : C.I₀, IsReduced (C.X i) := fun i ↦ by
    have := hIntegral i
    infer_instance
  have : IsReduced T := IsReduced.of_openCover T C
  let s := allOnesProjPoint R K σ
  have hs (i : σ) : Set.range s ⊆ Set.range (standardCoordinateChartMap R σ i) := by
    rintro _ ⟨x, rfl⟩
    change s x ∈ (standardCoordinateChartMap R σ i).opensRange
    rw [standardCoordinateChartMap_opensRange]
    have hx : x ∈ s ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) := by
      change x ∈ allOnesProjPoint R K σ ⁻¹ᵁ _
      rw [allOnesProjPoint_preimage_basicOpen]
      trivial
    exact hx
  let l (i : σ) : Spec (CommRingCat.of K) ⟶
      Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} R)) :=
    IsOpenImmersion.lift (standardCoordinateChartMap R σ i) s (hs i)
  have hl (i : σ) : l i ≫ standardCoordinateChartMap R σ i = s :=
    IsOpenImmersion.lift_fac (standardCoordinateChartMap R σ i) s (hs i)
  let t : Spec (CommRingCat.of K) ⟶ T :=
    pullback.lift s (𝟙 _) (by simpa [s, p, y] using allOnesProjPoint_toSpec R K σ)
  have hli (i : σ) : l i ≫ (standardCoordinateChartMap R σ i ≫ p) = (𝟙 _) ≫ y := by
    rw [← Category.assoc, hl]
    simpa [s, p, y] using allOnesProjPoint_toSpec R K σ
  let ti (i : σ) : Spec (CommRingCat.of K) ⟶ C.X i :=
    pullback.lift (l i) (𝟙 _) (hli i)
  have hti (i : σ) : ti i ≫ C.f i = t := by
    apply pullback.hom_ext
    · have hfst : C.f i ≫ pullback.fst p y =
          pullback.fst (standardCoordinateChartMap R σ i ≫ p) y ≫
            standardCoordinateChartMap R σ i :=
        pullbackOpenCoverOfLeft_fst
          (standardCoordinateAffineOpenCover R σ).openCover p y i
      calc
        (ti i ≫ C.f i) ≫ pullback.fst p y =
            ti i ≫
              (pullback.fst (standardCoordinateChartMap R σ i ≫ p) y ≫
                standardCoordinateChartMap R σ i) :=
          (Category.assoc (ti i) (C.f i) (pullback.fst p y)).trans
            (congrArg
              (fun k : C.X i ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ↦
                ti i ≫ k) hfst)
        _ = (ti i ≫ pullback.fst (standardCoordinateChartMap R σ i ≫ p) y) ≫
              standardCoordinateChartMap R σ i :=
          (Category.assoc (ti i)
            (pullback.fst (standardCoordinateChartMap R σ i ≫ p) y)
            (standardCoordinateChartMap R σ i)).symm
        _ = l i ≫ standardCoordinateChartMap R σ i :=
          congrArg
            (fun k : Spec (CommRingCat.of K) ⟶
                Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} R)) ↦
              k ≫ standardCoordinateChartMap R σ i)
            (pullback.lift_fst (f := standardCoordinateChartMap R σ i ≫ p) (g := y)
              (l i) (𝟙 _) (hli i))
        _ = t ≫ pullback.fst p y :=
          (hl i).trans
            (pullback.lift_fst (f := p) (g := y) s (𝟙 _)
              (by simpa [s, p, y] using allOnesProjPoint_toSpec R K σ)).symm
    · have hsnd : C.f i ≫ pullback.snd p y =
          pullback.snd (standardCoordinateChartMap R σ i ≫ p) y :=
        pullbackOpenCoverOfLeft_snd
          (standardCoordinateAffineOpenCover R σ).openCover p y i
      calc
        (ti i ≫ C.f i) ≫ pullback.snd p y =
            ti i ≫ pullback.snd (standardCoordinateChartMap R σ i ≫ p) y :=
          (Category.assoc (ti i) (C.f i) (pullback.snd p y)).trans
            (congrArg (fun k : C.X i ⟶ Spec (CommRingCat.of K) ↦ ti i ≫ k) hsnd)
        _ = 𝟙 (Spec (CommRingCat.of K)) :=
          pullback.lift_snd (f := standardCoordinateChartMap R σ i ≫ p) (g := y)
            (l i) (𝟙 _) (hli i)
        _ = t ≫ pullback.snd p y :=
          (pullback.lift_snd (f := p) (g := y) s (𝟙 _)
            (by simpa [s, p, y] using allOnesProjPoint_toSpec R K σ)).symm
  let q : Spec (CommRingCat.of K) := Classical.choice inferInstance
  let z : T := t q
  have hz (i : σ) : z ∈ (C.f i).opensRange := by
    refine ⟨ti i q, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (CommRingCat.of K) ⟶ T ↦ f q) (hti i)
  have hpre (i : σ) : PreirreducibleSpace (C.f i).opensRange := by
    apply Subtype.preirreducibleSpace
    change IsPreirreducible (Set.range (C.f i))
    rw [← Set.image_univ]
    exact PreirreducibleSpace.isPreirreducible_univ.image _ (C.f i).continuous.continuousOn
  have : PreirreducibleSpace T := PreirreducibleSpace.of_isOpenCover
    (U := fun i : σ ↦ (C.f i).opensRange) (by
      intro i j _ h
      have hb : z ∈ (⊥ : TopologicalSpace.Opens T) := h.le_bot ⟨hz i, hz j⟩
      simp at hb) C.isOpenCover_opensRange hpre
  have : IrreducibleSpace T :=
    { toPreirreducibleSpace := inferInstance, toNonempty := ⟨z⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced T

/-- The coefficient morphism of projective space with finitely many nonempty
homogeneous coordinates is geometrically integral over any commutative ring. -/
theorem polynomialProjToSpec_geometricallyIntegral_of_finite
    (R : Type (max u v)) [CommRing R] (σ : Type v) [Finite σ] [Nonempty σ] :
    GeometricallyIntegral (polynomialProjToSpec R σ) := by
  classical
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (IsIntegral : Scheme.{max u v} → Prop) :=
    ⟨fun e _ ↦ IsIntegral.of_isIso e.hom⟩
  rw [GeometricallyIntegral.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact isIntegral_standardCoordinatePullback R K σ

/-- Every finite-dimensional projective space is geometrically integral over
its coefficient ring. -/
theorem polynomialProjToSpec_fin_geometricallyIntegral
    (R : Type u) [CommRing R] (n : ℕ) :
    GeometricallyIntegral (polynomialProjToSpec R (Fin (n + 1))) := by
  exact polynomialProjToSpec_geometricallyIntegral_of_finite R (Fin (n + 1))

end ProjectiveSpace
