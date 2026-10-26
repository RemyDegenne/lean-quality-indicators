/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import SphereTopology.Homology.Singular.Reduced

/-!
# Reduced Mayer--Vietoris in degrees one and zero for two open sets

This file restricts the integral two-open Mayer--Vietoris sequence to
the augmentation kernels in degree zero. The ordered convention remains
`c ↦ (c,-c)`, so reversing the cover negates the connecting morphism after
the sign-free swap of the intersection.

## Implementation notes

Coefficients are integral, and degrees are nonnegative: reduced degree-zero
homology is the augmentation kernel. The sum from the reduced homology of the
opens to that of the ambient space is epic when the intersection is nonempty.
Without that hypothesis, a disjoint cover by two nonempty opens can have zero
reduced degree-zero homology on each open but nonzero reduced degree-zero
homology on the ambient space. Exactness at the reduced biproduct does not
require a nonempty intersection. These are two-open singular-homology statements,
not statements about arbitrary coefficients or axiomatic homology theories.
May's reduced theory is based-relative, uses compactly generated constructions,
and displays diagonal/difference maps. Identifying it with this augmentation-kernel
theory requires the corresponding basepoint, topology and sign comparisons.

## References

* J. P. May, *A concise course in algebraic topology*, Chapter 14, §§1 and 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

private noncomputable def twoOpenIntersectionHomologyFunctorIso
    {X : TopCat.{u}} (U V : Opens X) (n : ℕ) :
    (integralSingularHomologyFunctor n).obj
        ((Opens.toTopCat X).obj (U ⊓ V)) ≅
      (twoOpenSmallShortComplex U V).X₁.homology n :=
  Iso.refl _

private noncomputable def twoOpenReducedMayerVietorisδToHomologyZero
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    TopCat.reducedSingularHomology X 1 ⟶
      (integralSingularHomologyFunctor 0).obj
        ((Opens.toTopCat X).obj (U ⊓ V)) :=
  (TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom ≫
    twoOpenMayerVietorisδ U V hUV 0 ≫
    (twoOpenIntersectionHomologyFunctorIso U V 0).inv

private theorem twoOpenReducedMayerVietorisδToHomologyZero_augmentation
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    twoOpenReducedMayerVietorisδToHomologyZero U V hUV ≫
        ((Opens.toTopCat X).obj (U ⊓ V)).singularHomology₀ε
          TopCat.singularHomologyIntegerCoefficients = 0 := by
  have hδ := twoOpenMayerVietorisδ_comp U V hUV 0
  have hδDifference : twoOpenMayerVietorisδ U V hUV 0 ≫
      twoOpenMayerVietorisFromIntersection U V 0 = 0 := by
    change (twoOpenMayerVietorisδ U V hUV 0 ≫
      HomologicalComplex.homologyMap
        (twoOpenSmallShortComplex U V).f 0) ≫
      (twoOpenMiddleHomologyIso U V 0).hom = 0
    rw [hδ, zero_comp]
  have hLeft := twoOpenMayerVietorisFromIntersection_fst U V 0
  have hAugmentation := TopCat.singularHomologyZeroAugmentation_naturality
    (twoOpenIntersectionToLeft U V)
  rw [integralSingularHomologyFunctor_map] at hAugmentation
  let s := (TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom
  let d := twoOpenMayerVietorisδ U V hUV 0
  let a := s ≫ d
  let i := (twoOpenIntersectionHomologyFunctorIso U V 0).inv
  let l := HomologicalComplex.homologyMap
    (integralSingularChainMap (twoOpenIntersectionToLeft U V)) 0
  let m := twoOpenMayerVietorisFromIntersection U V 0
  let p := (biprod.fst :
    (integralSingularHomology ((Opens.toTopCat X).obj U) 0 ⊞
      integralSingularHomology ((Opens.toTopCat X).obj V) 0) ⟶ _)
  let εQ := ((Opens.toTopCat X).obj (U ⊓ V)).singularHomology₀ε
    TopCat.singularHomologyIntegerCoefficients
  let εU := ((Opens.toTopCat X).obj U).singularHomology₀ε
    TopCat.singularHomologyIntegerCoefficients
  change (a ≫ i) ≫ εQ = 0
  have ha : a ≫ m = 0 := by
    change (s ≫ d) ≫ m = 0
    calc
      _ = s ≫ (d ≫ m) := Category.assoc _ _ _
      _ = s ≫ 0 := congrArg (s ≫ ·) hδDifference
      _ = 0 := comp_zero
  calc
    (a ≫ i) ≫ εQ = (a ≫ i) ≫ (l ≫ εU) :=
      congrArg ((a ≫ i) ≫ ·) hAugmentation.symm
    _ = ((a ≫ i) ≫ l) ≫ εU := (Category.assoc _ _ _).symm
    _ = (a ≫ (i ≫ l)) ≫ εU :=
      congrArg (· ≫ εU) (Category.assoc _ _ _)
    _ = (a ≫ (m ≫ p)) ≫ εU :=
      congrArg (fun k ↦ (a ≫ k) ≫ εU) hLeft.symm
    _ = ((a ≫ m) ≫ p) ≫ εU := by
      rw [Category.assoc a m p]
    _ = 0 := by
      rw [ha, zero_comp]
      change (0 : TopCat.reducedSingularHomology X 1 ⟶
        (integralSingularHomologyFunctor 0).obj
          ((Opens.toTopCat X).obj U)) ≫ εU =
        (0 : TopCat.reducedSingularHomology X 1 ⟶
          TopCat.singularHomologyIntegerCoefficients)
      exact HasZeroMorphisms.zero_comp _ εU

/-- The reduced degree-zero connecting morphism for the ordered cover `(U,V)`.
It is the unique factorization of the ordinary connecting morphism
through the degree-zero augmentation kernel. -/
@[no_expose]
noncomputable def twoOpenReducedMayerVietorisδZero {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology ((Opens.toTopCat X).obj (U ⊓ V)) 0 :=
  kernel.lift
      (((Opens.toTopCat X).obj (U ⊓ V)).singularHomology₀ε
        TopCat.singularHomologyIntegerCoefficients)
      (twoOpenReducedMayerVietorisδToHomologyZero U V hUV)
      (twoOpenReducedMayerVietorisδToHomologyZero_augmentation U V hUV) ≫
    (TopCat.reducedSingularHomologyZeroIso
      ((Opens.toTopCat X).obj (U ⊓ V))).inv

private theorem twoOpenReducedMayerVietorisδZero_functor {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        (TopCat.reducedSingularHomologyZeroIso
          ((Opens.toTopCat X).obj (U ⊓ V))).hom ≫
        TopCat.reducedSingularHomologyZeroι
          ((Opens.toTopCat X).obj (U ⊓ V)) ≫
        (twoOpenIntersectionHomologyFunctorIso U V 0).hom =
      (TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom ≫
        twoOpenMayerVietorisδ U V hUV 0 := by
  unfold twoOpenReducedMayerVietorisδZero
  rw [Category.assoc]
  rw [(TopCat.reducedSingularHomologyZeroIso
    ((Opens.toTopCat X).obj (U ⊓ V))).inv_hom_id_assoc]
  let Q := (Opens.toTopCat X).obj (U ⊓ V)
  let εQ := Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients
  let k := twoOpenReducedMayerVietorisδToHomologyZero U V hUV
  have hk : kernel.lift εQ k
      (twoOpenReducedMayerVietorisδToHomologyZero_augmentation U V hUV) ≫
        kernel.ι εQ = k :=
    kernel.lift_ι εQ k
      (twoOpenReducedMayerVietorisδToHomologyZero_augmentation U V hUV)
  calc
    _ = k ≫ (twoOpenIntersectionHomologyFunctorIso U V 0).hom :=
      congrArg (· ≫ (twoOpenIntersectionHomologyFunctorIso U V 0).hom) hk
    _ = _ := by
      unfold k twoOpenReducedMayerVietorisδToHomologyZero
      let s := (TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom
      let d := twoOpenMayerVietorisδ U V hUV 0
      let e := twoOpenIntersectionHomologyFunctorIso U V 0
      change (s ≫ (d ≫ e.inv)) ≫ e.hom = s ≫ d
      calc
        _ = s ≫ ((d ≫ e.inv) ≫ e.hom) := Category.assoc _ _ _
        _ = s ≫ (d ≫ (e.inv ≫ e.hom)) :=
          congrArg (s ≫ ·) (Category.assoc _ _ _)
        _ = s ≫ (d ≫ 𝟙 _) := congrArg (fun q ↦ s ≫ (d ≫ q)) e.inv_hom_id
        _ = s ≫ d := congrArg (s ≫ ·) (Category.comp_id d)

/-- Composing the reduced connecting morphism with the augmentation-kernel
inclusion and open-subspace intersection identification recovers the
ordinary connecting morphism with the ordered difference/sum sign. -/
@[reassoc]
theorem twoOpenReducedMayerVietorisδZero_ordinary {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyZeroToOrdinary
          ((Opens.toTopCat X).obj (U ⊓ V)) ≫
        (twoOpenIntersectionHomologyIso U V 0).hom =
      (TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom ≫
        twoOpenMayerVietorisδ U V hUV 0 := by
  exact twoOpenReducedMayerVietorisδZero_functor U V hUV

/-- The ordered reduced degree-zero difference map
`H̃₀(U∩V) → H̃₀(U) ⊕ H̃₀(V)`, with convention `(c,-c)`. -/
noncomputable def twoOpenReducedMayerVietorisFromIntersectionZero
    {X : TopCat.{u}} (U V : Opens X) :
    TopCat.reducedSingularHomology
        ((Opens.toTopCat X).obj (U ⊓ V)) 0 ⟶
      TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0 ⊞
        TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 0 :=
  biprod.lift
    (TopCat.reducedSingularHomologyMap
      (twoOpenIntersectionToLeft U V) 0)
    (-TopCat.reducedSingularHomologyMap
      (twoOpenIntersectionToRight U V) 0)

private theorem twoOpenReducedMayerVietorisFromIntersectionZero_ordinary
    {X : TopCat.{u}} (U V : Opens X) :
    twoOpenReducedMayerVietorisFromIntersectionZero U V ≫
        biprod.map
          (TopCat.reducedSingularHomologyZeroToOrdinary
            ((Opens.toTopCat X).obj U))
          (TopCat.reducedSingularHomologyZeroToOrdinary
            ((Opens.toTopCat X).obj V)) =
      TopCat.reducedSingularHomologyZeroToOrdinary
          ((Opens.toTopCat X).obj (U ⊓ V)) ≫
        (twoOpenIntersectionHomologyIso U V 0).hom ≫
        twoOpenMayerVietorisFromIntersection U V 0 := by
  apply biprod.hom_ext
  · unfold twoOpenReducedMayerVietorisFromIntersectionZero
    rw [Category.assoc, biprod.map_fst]
    rw [biprod.lift_fst_assoc]
    rw [TopCat.reducedSingularHomologyZeroToOrdinary_naturality]
    simp only [Category.assoc]
    rw [twoOpenMayerVietorisFromIntersection_fst]
    simp only [Iso.hom_inv_id_assoc]
  · unfold twoOpenReducedMayerVietorisFromIntersectionZero
    rw [Category.assoc, biprod.map_snd]
    rw [biprod.lift_snd_assoc]
    rw [Preadditive.neg_comp]
    rw [TopCat.reducedSingularHomologyZeroToOrdinary_naturality]
    simp only [Category.assoc]
    rw [twoOpenMayerVietorisFromIntersection_snd]
    simp only [Iso.hom_inv_id_assoc, Preadditive.comp_neg]

/-- The sum on reduced degree-zero homology induced by the inclusions of
`U` and `V` in the ambient space, with a positive sign on each summand. -/
noncomputable def twoOpenReducedMayerVietorisFromBiprodZero
    {X : TopCat.{u}} (U V : Opens X) :
    TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0 ⊞
        TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 0 ⟶
      TopCat.reducedSingularHomology X 0 :=
  biprod.desc
    (TopCat.reducedSingularHomologyMap U.inclusion' 0)
    (TopCat.reducedSingularHomologyMap V.inclusion' 0)

/-- The first component of the reduced sum is induced by the inclusion of `U`. -/
@[reassoc (attr := simp)]
theorem twoOpenReducedMayerVietorisFromBiprodZero_inl
    {X : TopCat.{u}} (U V : Opens X) :
    biprod.inl ≫ twoOpenReducedMayerVietorisFromBiprodZero U V =
      TopCat.reducedSingularHomologyMap U.inclusion' 0 := by
  exact biprod.inl_desc _ _

/-- The second component of the reduced sum is induced by the inclusion of `V`,
also with a positive sign. -/
@[reassoc (attr := simp)]
theorem twoOpenReducedMayerVietorisFromBiprodZero_inr
    {X : TopCat.{u}} (U V : Opens X) :
    biprod.inr ≫ twoOpenReducedMayerVietorisFromBiprodZero U V =
      TopCat.reducedSingularHomologyMap V.inclusion' 0 := by
  exact biprod.inr_desc _ _

/-- The reduced sum agrees with the ordinary Mayer--Vietoris sum after the
augmentation-kernel inclusions. -/
@[reassoc]
theorem twoOpenReducedMayerVietorisFromBiprodZero_ordinary
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    twoOpenReducedMayerVietorisFromBiprodZero U V ≫
        TopCat.reducedSingularHomologyZeroToOrdinary X =
      biprod.map
          (TopCat.reducedSingularHomologyZeroToOrdinary
            ((Opens.toTopCat X).obj U))
          (TopCat.reducedSingularHomologyZeroToOrdinary
            ((Opens.toTopCat X).obj V)) ≫
        twoOpenMayerVietorisFromBiprod U V hUV 0 := by
  rw [twoOpenMayerVietorisFromBiprod_eq]
  apply biprod.hom_ext'
  · simpa only [twoOpenReducedMayerVietorisFromBiprodZero_inl_assoc,
      biprod.inl_map_assoc, biprod.inl_desc] using
        TopCat.reducedSingularHomologyZeroToOrdinary_naturality U.inclusion'
  · simpa only [twoOpenReducedMayerVietorisFromBiprodZero_inr_assoc,
      biprod.inr_map_assoc, biprod.inr_desc] using
        TopCat.reducedSingularHomologyZeroToOrdinary_naturality V.inclusion'

/-- Naturality of the reduced sum for a continuous map respecting the ordered
pair of open subsets. Neither ordered pair needs to cover its ambient space. -/
@[reassoc]
theorem twoOpenReducedMayerVietorisFromBiprodZero_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    twoOpenReducedMayerVietorisFromBiprodZero U V ≫
        TopCat.reducedSingularHomologyMap f 0 =
      biprod.map
          (TopCat.reducedSingularHomologyMap (TopCat.openMap f U U' hU) 0)
          (TopCat.reducedSingularHomologyMap (TopCat.openMap f V V' hV) 0) ≫
        twoOpenReducedMayerVietorisFromBiprodZero U' V' := by
  apply biprod.hom_ext'
  · simp only [twoOpenReducedMayerVietorisFromBiprodZero_inl_assoc,
      biprod.inl_map_assoc, twoOpenReducedMayerVietorisFromBiprodZero_inl]
    rw [← Functor.map_comp, ← Functor.map_comp, TopCat.openMap_comp_inclusion]
  · simp only [twoOpenReducedMayerVietorisFromBiprodZero_inr_assoc,
      biprod.inr_map_assoc, twoOpenReducedMayerVietorisFromBiprodZero_inr]
    rw [← Functor.map_comp, ← Functor.map_comp, TopCat.openMap_comp_inclusion]

/-- The ordered reduced difference followed by the reduced sum is zero. -/
@[reassoc (attr := simp)]
theorem twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod
    {X : TopCat.{u}} (U V : Opens X) :
    twoOpenReducedMayerVietorisFromIntersectionZero U V ≫
      twoOpenReducedMayerVietorisFromBiprodZero U V = 0 := by
  simp only [twoOpenReducedMayerVietorisFromIntersectionZero,
    twoOpenReducedMayerVietorisFromBiprodZero, biprod.lift_desc,
    Preadditive.neg_comp, ← Functor.map_comp]
  rw [twoOpenIntersectionToLeft_comp, twoOpenIntersectionToRight_comp]
  exact add_neg_cancel _

/-- The integral reduced Mayer--Vietoris sequence of a two-open cover is exact
at `H̃₀(U) ⊕ H̃₀(V)`, even when the intersection is empty.

This is the reduced degree-zero counterpart of the ordinary Mayer--Vietoris
sequence in May, *A concise course in algebraic topology*, Chapter 14, §5. -/
theorem twoOpenReducedMayerVietoris_exact_biprodZero
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (ShortComplex.mk
      (twoOpenReducedMayerVietorisFromIntersectionZero U V)
      (twoOpenReducedMayerVietorisFromBiprodZero U V)
      (twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod U V)).Exact := by
  let S := ShortComplex.mk
    (twoOpenReducedMayerVietorisFromIntersectionZero U V)
    (twoOpenReducedMayerVietorisFromBiprodZero U V)
    (twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod U V)
  apply (ShortComplex.moduleCat_exact_iff S).2
  intro x hx
  let j := biprod.map
    (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj U))
    (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj V))
  let T := ShortComplex.mk
    (twoOpenMayerVietorisFromIntersection U V 0)
    (twoOpenMayerVietorisFromBiprod U V hUV 0)
    (twoOpenMayerVietorisFromIntersection_comp_fromBiprod U V hUV 0)
  have hT : T.Exact := twoOpenMayerVietoris_exact_at_biprod U V hUV 0
  let π : S.X₂ ⟶ TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0 := biprod.fst
  let πOrd : T.X₂ ⟶ integralSingularHomology ((Opens.toTopCat X).obj U) 0 := biprod.fst
  have hxOrd : T.g (j x) = 0 := by
    have h := congrArg (fun q ↦ q x)
      (twoOpenReducedMayerVietorisFromBiprodZero_ordinary U V hUV)
    change TopCat.reducedSingularHomologyZeroToOrdinary X (S.g x) = T.g (j x) at h
    rw [hx, map_zero] at h
    exact h.symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).1 hT _ hxOrd
  let Q := (Opens.toTopCat X).obj (U ⊓ V)
  let e := twoOpenIntersectionHomologyIso U V 0
  let y₀ := e.inv y
  let l := HomologicalComplex.homologyMap
    (integralSingularChainMap (twoOpenIntersectionToLeft U V)) 0
  have hyLeft : l y₀ =
      TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat X).obj U) (π x) := by
    have h := congrArg (fun q ↦ q y)
      (twoOpenMayerVietorisFromIntersection_fst U V 0)
    change πOrd (T.f y) = l y₀ at h
    rw [hy] at h
    have hj := congrArg (fun q ↦ q x) (biprod.map_fst
      (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj U))
      (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj V)))
    change πOrd (j x) =
      TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat X).obj U) (π x) at hj
    exact h.symm.trans hj
  -- The first coordinate of the ordinary preimage forces its augmentation to vanish.
  have hyAug : Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients y₀ = 0 := by
    have hAug := TopCat.singularHomologyZeroAugmentation_naturality
      (twoOpenIntersectionToLeft U V)
    rw [integralSingularHomologyFunctor_map] at hAug
    have h := congrArg (fun q ↦ q y₀) hAug
    change ((Opens.toTopCat X).obj U).singularHomology₀ε
        TopCat.singularHomologyIntegerCoefficients (l y₀) =
      Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients y₀ at h
    rw [hyLeft] at h
    have hk := congrArg (fun q ↦ q (π x))
      (TopCat.reducedSingularHomologyZeroToOrdinary_augmentation
        ((Opens.toTopCat X).obj U))
    exact h.symm.trans hk
  let C := ShortComplex.mk (TopCat.reducedSingularHomologyZeroToOrdinary Q)
    (Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients)
    (TopCat.reducedSingularHomologyZeroToOrdinary_augmentation Q)
  have hC : C.Exact := ShortComplex.exact_of_f_is_kernel C
    (TopCat.reducedSingularHomologyZeroToOrdinaryIsKernel Q)
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff C).1 hC _ hyAug
  refine ⟨z, ?_⟩
  apply (ModuleCat.mono_iff_injective j).1 inferInstance
  have h := congrArg (fun q ↦ q z)
    (twoOpenReducedMayerVietorisFromIntersectionZero_ordinary U V)
  change j (S.f z) = T.f (e.hom (C.f z)) at h
  rw [hz] at h
  have he : e.hom y₀ = y := Iso.inv_hom_id_apply e y
  rw [he] at h
  exact h.trans hy

/-- The reduced degree-zero Mayer--Vietoris sum of a two-open cover is epic
when the intersection is nonempty. A common point makes the intersection's
augmentation epic. For the nonnegative reduced convention used here, disjoint
nonempty opens can instead leave a nonzero ambient reduced degree-zero group.

This is an integral two-open consequence of the reduced homology and
Mayer--Vietoris constructions in May, *A concise course in algebraic topology*,
Chapter 14, §§1 and 5, not the arbitrary-coefficient axiomatic theorem. -/
theorem twoOpenReducedMayerVietorisFromBiprodZero_epi
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hC : Nonempty ((Opens.toTopCat X).obj (U ⊓ V))) :
    Epi (twoOpenReducedMayerVietorisFromBiprodZero U V) := by
  classical
  let A := (Opens.toTopCat X).obj U
  let B := (Opens.toTopCat X).obj V
  let Q := (Opens.toTopCat X).obj (U ⊓ V)
  let ε (Y : TopCat.{u}) : integralSingularHomology Y 0 ⟶
      TopCat.singularHomologyIntegerCoefficients :=
    Y.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients
  let ι (Y : TopCat.{u}) := TopCat.reducedSingularHomologyZeroToOrdinary Y
  let K (Y : TopCat.{u}) := ShortComplex.mk (ι Y) (ε Y)
    (TopCat.reducedSingularHomologyZeroToOrdinary_augmentation Y)
  have hK (Y : TopCat.{u}) : (K Y).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (TopCat.reducedSingularHomologyZeroToOrdinaryIsKernel Y)
  let f := twoOpenMayerVietorisFromIntersection U V 0
  let g := twoOpenMayerVietorisFromBiprod U V hUV 0
  let e := twoOpenIntersectionHomologyIso U V 0
  let P : ModuleCat.{u} ℤ :=
    integralSingularHomology A 0 ⊞ integralSingularHomology B 0
  let R : ModuleCat.{u} ℤ :=
    TopCat.reducedSingularHomology A 0 ⊞ TopCat.reducedSingularHomology B 0
  let πA : P ⟶ integralSingularHomology A 0 := biprod.fst
  let πB : P ⟶ integralSingularHomology B 0 := biprod.snd
  let iA : TopCat.reducedSingularHomology A 0 ⟶ R := biprod.inl
  let iB : TopCat.reducedSingularHomology B 0 ⟶ R := biprod.inr
  let kA : integralSingularHomology A 0 ⟶ P := biprod.inl
  let kB : integralSingularHomology B 0 ⟶ P := biprod.inr
  let j : R ⟶ P := biprod.map (ι A) (ι B)
  let : Epi g := by
    let : Epi (twoOpenSmallShortComplex U V).g :=
      (twoOpenSmallShortExact U V).epi_g
    let : Epi (HomologicalComplex.homologyMap
        (twoOpenSmallShortComplex U V).g 0) :=
      HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
    dsimp only [g, twoOpenMayerVietorisFromBiprod, twoOpenMayerVietorisToSpace]
    infer_instance
  have hfg : f ≫ g = 0 :=
    twoOpenMayerVietorisFromIntersection_comp_fromBiprod U V hUV 0
  have hAU : HomologicalComplex.homologyMap
      (integralSingularChainMap U.inclusion') 0 ≫ ε X = ε A := by
    have h := TopCat.singularHomologyZeroAugmentation_naturality U.inclusion'
    rw [integralSingularHomologyFunctor_map] at h
    exact h
  have hAV : HomologicalComplex.homologyMap
      (integralSingularChainMap V.inclusion') 0 ≫ ε X = ε B := by
    have h := TopCat.singularHomologyZeroAugmentation_naturality V.inclusion'
    rw [integralSingularHomologyFunctor_map] at h
    exact h
  have hsum : g ≫ ε X = biprod.desc (ε A) (ε B) := by
    dsimp only [g]
    rw [twoOpenMayerVietorisFromBiprod_eq]
    apply biprod.hom_ext'
    · simpa only [biprod.inl_desc_assoc, biprod.inl_desc] using hAU
    · simpa only [biprod.inr_desc_assoc, biprod.inr_desc] using hAV
  let l : integralSingularHomology Q 0 ⟶ integralSingularHomology A 0 :=
    HomologicalComplex.homologyMap
      (integralSingularChainMap (twoOpenIntersectionToLeft U V)) 0
  let r : integralSingularHomology Q 0 ⟶ integralSingularHomology B 0 :=
    HomologicalComplex.homologyMap
      (integralSingularChainMap (twoOpenIntersectionToRight U V)) 0
  have hAIntersection : l ≫ ε A = ε Q := by
    have h := TopCat.singularHomologyZeroAugmentation_naturality
      (twoOpenIntersectionToLeft U V)
    rw [integralSingularHomologyFunctor_map] at h
    exact h
  have hBIntersection : r ≫ ε B = ε Q := by
    have h := TopCat.singularHomologyZeroAugmentation_naturality
      (twoOpenIntersectionToRight U V)
    rw [integralSingularHomologyFunctor_map] at h
    exact h
  have hfst : (f ≫ πA) ≫ ε A = e.inv ≫ ε Q := by
    calc
      (f ≫ πA) ≫ ε A = (e.inv ≫ l) ≫ ε A :=
        congrArg (· ≫ ε A) (twoOpenMayerVietorisFromIntersection_fst U V 0)
      _ = e.inv ≫ (l ≫ ε A) := Category.assoc _ _ _
      _ = e.inv ≫ ε Q := congrArg (e.inv ≫ ·) hAIntersection
  have hsnd : (f ≫ πB) ≫ ε B = -(e.inv ≫ ε Q) := by
    calc
      (f ≫ πB) ≫ ε B = (e.inv ≫ (-r)) ≫ ε B :=
        congrArg (· ≫ ε B) (twoOpenMayerVietorisFromIntersection_snd U V 0)
      _ = e.inv ≫ ((-r) ≫ ε B) := Category.assoc _ _ _
      _ = e.inv ≫ (-(r ≫ ε B)) :=
        congrArg (e.inv ≫ ·) (Preadditive.neg_comp r (ε B))
      _ = e.inv ≫ (-(ε Q)) := congrArg (fun k ↦ e.inv ≫ (-k)) hBIntersection
      _ = -(e.inv ≫ ε Q) := Preadditive.comp_neg _ _
  apply (ModuleCat.epi_iff_surjective _).2
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective g).1 inferInstance (ι X x)
  have haug : ε A (πA y) + ε B (πB y) = 0 := by
    have h := congrArg (fun q ↦ q y) hsum
    rw [biprod.desc_eq] at h
    change ε X (g y) = ε A (πA y) + ε B (πB y) at h
    rw [hy] at h
    have hx := congrArg (fun q ↦ q x)
      (TopCat.reducedSingularHomologyZeroToOrdinary_augmentation X)
    change ε X (ι X x) = 0 at hx
    exact h.symm.trans hx
  -- Remove the augmentation pair `(t,-t)` using a point of the intersection.
  let t := ε A (πA y)
  let p : Q := Classical.choice hC
  let q : integralSingularHomology Q 0 := TopCat.singularHomologyZeroPoint Q p t
  let c := e.hom q
  have hpt : ε Q q = t :=
    congrArg (fun k ↦ k t) (TopCat.singularHomologyZeroPoint_augmentation Q p)
  have he : e.inv c = q := Iso.hom_inv_id_apply e q
  have hcQ : ε Q (e.inv c) = t :=
    (congrArg (fun v ↦ ε Q v) he).trans hpt
  have hcA : ε A (πA (f c)) = t := by
    have h := congrArg (fun k ↦ k c) hfst
    change ε A (πA (f c)) = ε Q (e.inv c) at h
    exact h.trans hcQ
  have hcB : ε B (πB (f c)) = -t := by
    have h := congrArg (fun k ↦ k c) hsnd
    change ε B (πB (f c)) = -(ε Q (e.inv c)) at h
    exact h.trans (congrArg Neg.neg hcQ)
  let z := y - f c
  have hzA : ε A (πA z) = 0 := by
    dsimp only [z]
    rw [map_sub, map_sub, hcA]
    exact sub_self _
  have hzB : ε B (πB z) = 0 := by
    dsimp only [z]
    rw [map_sub, map_sub, hcB]
    have hB : ε B (πB y) = -t := eq_neg_of_add_eq_zero_right haug
    rw [hB, sub_self]
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff (K A)).1 (hK A) _ hzA
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff (K B)).1 (hK B) _ hzB
  change ι A a = πA z at ha
  change ι B b = πB z at hb
  let w : R := iA a + iB b
  have hjw : j w = z := by
    have hja := congrArg (fun k ↦ k a) (biprod.inl_map (ι A) (ι B))
    have hjb := congrArg (fun k ↦ k b) (biprod.inr_map (ι A) (ι B))
    change j (iA a) = kA (ι A a) at hja
    change j (iB b) = kB (ι B b) at hjb
    change j (iA a + iB b) = z
    rw [map_add, hja, hjb, ha, hb]
    exact congrArg (fun k ↦ k z)
      (biprod.total : πA ≫ kA + πB ≫ kB = 𝟙 P)
  refine ⟨w, ?_⟩
  apply (ModuleCat.mono_iff_injective (ι X)).1 inferInstance
  have h := congrArg (fun q ↦ q w)
    (twoOpenReducedMayerVietorisFromBiprodZero_ordinary U V hUV)
  change ι X (twoOpenReducedMayerVietorisFromBiprodZero U V w) = g (j w) at h
  rw [h, hjw]
  change g (y - f c) = ι X x
  have hfc : g (f c) = 0 := by
    change (f ≫ g) c = 0
    rw [hfg]
    rfl
  rw [map_sub, hy, hfc, sub_zero]

/-- The reduced connecting morphism is followed by zero in the reduced
degree-zero Mayer--Vietoris sequence. -/
@[reassoc]
theorem twoOpenReducedMayerVietorisδZero_comp_fromIntersection
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
      twoOpenReducedMayerVietorisFromIntersectionZero U V = 0 := by
  apply (cancel_mono (biprod.map
    (TopCat.reducedSingularHomologyZeroToOrdinary
      ((Opens.toTopCat X).obj U))
    (TopCat.reducedSingularHomologyZeroToOrdinary
      ((Opens.toTopCat X).obj V)))).1
  rw [Category.assoc,
    twoOpenReducedMayerVietorisFromIntersectionZero_ordinary]
  rw [twoOpenReducedMayerVietorisδZero_ordinary_assoc]
  change _ ≫ (twoOpenMayerVietorisδ U V hUV 0 ≫
    HomologicalComplex.homologyMap
      (twoOpenSmallShortComplex U V).f 0 ≫
    (twoOpenMiddleHomologyIso U V 0).hom) = _
  rw [twoOpenMayerVietorisδ_comp_assoc, zero_comp, comp_zero, zero_comp]

/-- Exactness at the reduced degree-zero homology of the
intersection as an open subspace. -/
theorem twoOpenReducedMayerVietoris_exact_intersectionZero
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (ShortComplex.mk
      (twoOpenReducedMayerVietorisδZero U V hUV)
      (twoOpenReducedMayerVietorisFromIntersectionZero U V)
      (twoOpenReducedMayerVietorisδZero_comp_fromIntersection U V hUV)).Exact := by
  let S := ShortComplex.mk
    (twoOpenReducedMayerVietorisδZero U V hUV)
    (twoOpenReducedMayerVietorisFromIntersectionZero U V)
    (twoOpenReducedMayerVietorisδZero_comp_fromIntersection U V hUV)
  apply (ShortComplex.moduleCat_exact_iff S).2
  intro x hx
  let T := ShortComplex.mk
    (twoOpenMayerVietorisδ U V hUV 0)
    (twoOpenMayerVietorisFromIntersection U V 0)
    (by
      change (twoOpenMayerVietorisδ U V hUV 0 ≫
        HomologicalComplex.homologyMap
          (twoOpenSmallShortComplex U V).f 0) ≫
        (twoOpenMiddleHomologyIso U V 0).hom = 0
      rw [twoOpenMayerVietorisδ_comp, zero_comp])
  have hT : T.Exact :=
    twoOpenMayerVietoris_exact_at_intersection U V hUV 0
  have hxOrd : T.g
      ((TopCat.reducedSingularHomologyZeroToOrdinary
          ((Opens.toTopCat X).obj (U ⊓ V)) ≫
        (twoOpenIntersectionHomologyIso U V 0).hom) x) = 0 := by
    have h := congrArg (fun q ↦ q x)
      (twoOpenReducedMayerVietorisFromIntersectionZero_ordinary U V)
    dsimp [S] at hx
    dsimp [T]
    change (biprod.map
        (TopCat.reducedSingularHomologyZeroToOrdinary
          ((Opens.toTopCat X).obj U))
        (TopCat.reducedSingularHomologyZeroToOrdinary
          ((Opens.toTopCat X).obj V)))
          (twoOpenReducedMayerVietorisFromIntersectionZero U V x) =
      T.g ((TopCat.reducedSingularHomologyZeroToOrdinary
          ((Opens.toTopCat X).obj (U ⊓ V)) ≫
        (twoOpenIntersectionHomologyIso U V 0).hom) x) at h
    rw [hx, map_zero] at h
    exact h.symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).1 hT _ hxOrd
  dsimp [T] at hy
  let e := TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)
  refine ⟨e.inv y, ?_⟩
  apply (ModuleCat.mono_iff_injective
    (TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat X).obj (U ⊓ V)) ≫
      (twoOpenIntersectionHomologyIso U V 0).hom)).1 inferInstance
  dsimp [S, e]
  have hδ := congrArg (fun q ↦ q (e.inv y))
    (twoOpenReducedMayerVietorisδZero_ordinary U V hUV)
  dsimp [e] at hδ
  rw [Iso.inv_hom_id_apply] at hδ
  exact hδ.trans hy

/-- Naturality of the reduced connecting morphism for a continuous map
respecting both ordered opens, stated using the restricted open-intersection
map. -/
theorem twoOpenReducedMayerVietorisδZero_naturality {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionMap f U V U' V' hU hV) 0 =
      TopCat.reducedSingularHomologyMap f 1 ≫
        twoOpenReducedMayerVietorisδZero U' V' hU'V' := by
  apply (cancel_mono
    (TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat Y).obj (U' ⊓ V')) ≫
      (twoOpenIntersectionHomologyIso U' V' 0).hom)).1
  simp only [Category.assoc]
  rw [TopCat.reducedSingularHomologyZeroToOrdinary_naturality_assoc]
  rw [← twoOpenIntersectionHomologyIso_naturality]
  rw [twoOpenReducedMayerVietorisδZero_ordinary_assoc]
  rw [twoOpenMayerVietorisδ_naturality_induced]
  all_goals try rw [← TopCat.reducedSingularHomologyMap_isoOfNeZero_assoc]
  rw [twoOpenReducedMayerVietorisδZero_ordinary]

/-- Swapping the ordered cover and transporting by the sign-free
open-subspace intersection swap negates the reduced connecting morphism. -/
theorem twoOpenReducedMayerVietorisδZero_swap_eq_neg {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionSwapMap U V) 0 =
      -(twoOpenReducedMayerVietorisδZero V U hVU) := by
  apply (cancel_mono
    (TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat X).obj (V ⊓ U)) ≫
      (twoOpenIntersectionHomologyIso V U 0).hom)).1
  simp only [Category.assoc]
  rw [TopCat.reducedSingularHomologyZeroToOrdinary_naturality_assoc]
  rw [← twoOpenIntersectionHomologyIso_swap]
  rw [twoOpenReducedMayerVietorisδZero_ordinary_assoc]
  rw [twoOpenMayerVietorisδ_swap_eq_neg U V hUV hVU 0]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]
  rw [twoOpenReducedMayerVietorisδZero_ordinary]

set_option linter.style.haveILetI false in
/-- If both opens have zero reduced homology in degrees zero and one, the
reduced connecting morphism is an isomorphism. -/
theorem twoOpenReducedMayerVietorisδZero_isIso_of_acyclic_opens
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hU₀ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0))
    (hV₀ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 0))
    (hU₁ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 1))
    (hV₁ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 1)) :
    IsIso (twoOpenReducedMayerVietorisδZero U V hUV) := by
  have hReducedExact :=
    twoOpenReducedMayerVietoris_exact_intersectionZero U V hUV
  have hReducedTarget : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0 ⊞
        TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 0) :=
    (biprod_isZero_iff _ _).2 ⟨hU₀, hV₀⟩
  letI : Epi (twoOpenReducedMayerVietorisδZero U V hUV) :=
    (hReducedExact.epi_f_iff).2
      (hReducedTarget.eq_of_tgt
        (twoOpenReducedMayerVietorisFromIntersectionZero U V) 0)
  have hU₁' : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj U) 1) :=
    hU₁.of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((Opens.toTopCat X).obj U) 1 (by simp)).symm
  have hV₁' : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj V) 1) :=
    hV₁.of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((Opens.toTopCat X).obj V) 1 (by simp)).symm
  have hOrdinarySource : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj U) 1 ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) 1) :=
    (biprod_isZero_iff _ _).2 ⟨hU₁', hV₁'⟩
  have hSpace := twoOpenMayerVietoris_exact_at_space U V hUV 0
  letI hOrdinaryMono : Mono (twoOpenMayerVietorisδ U V hUV 0) :=
    (hSpace.mono_g_iff).2
      (hOrdinarySource.eq_of_src
        (twoOpenMayerVietorisFromBiprod U V hUV 1) 0)
  letI hCompositeMono : Mono
      ((TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom ≫
        twoOpenMayerVietorisδ U V hUV 0) := mono_comp _ _
  letI : Mono (twoOpenReducedMayerVietorisδZero U V hUV) :=
    mono_of_mono_fac (twoOpenReducedMayerVietorisδZero_ordinary U V hUV)
  exact isIso_of_mono_of_epi _

/-- The reduced Mayer--Vietoris isomorphism furnished by an acyclic ordered
two-open cover in the adjacent degrees. -/
noncomputable def twoOpenReducedMayerVietorisIsoOfAcyclicOpens
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hU₀ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0))
    (hV₀ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 0))
    (hU₁ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 1))
    (hV₁ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 1)) :
    TopCat.reducedSingularHomology X 1 ≅
      TopCat.reducedSingularHomology
        ((Opens.toTopCat X).obj (U ⊓ V)) 0 := by
  letI := twoOpenReducedMayerVietorisδZero_isIso_of_acyclic_opens
    U V hUV hU₀ hV₀ hU₁ hV₁
  exact asIso (twoOpenReducedMayerVietorisδZero U V hUV)

end AlgebraicTopology
