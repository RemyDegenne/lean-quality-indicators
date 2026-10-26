/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.HomogeneousCoordinateChart
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Closed points of polynomial projective space

Over a field with finitely many coordinates, distinct vector-space projective
points define distinct points of polynomial `Proj`, and every such
homogeneous-coordinate point is closed.
Over an algebraically closed field with finitely many coordinates, every
closed point arises uniquely in this way.

The public API needs no decidable-equality assumption on the coordinate type.
-/

open AlgebraicGeometry CategoryTheory
open scoped ProjectiveSpace LinearAlgebra.Projectivization

public section

noncomputable section

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {ι : Type v} [Fintype ι]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι k

omit [IsAlgClosed k] in
private theorem polynomialProj_jacobsonSpace :
    JacobsonSpace (AlgebraicGeometry.Proj 𝒜) := by
  let U := standardCoordinateAffineOpenCover k ι
  rw [U.openCover.isOpenCover_opensRange.jacobsonSpace_iff]
  intro i
  have h : JacobsonSpace (U.openCover.X i) := by
    change JacobsonSpace (PrimeSpectrum (MvPolynomial {j : ι // j ≠ i} k))
    infer_instance
  let e := (U.openCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph
  exact .of_isClosedEmbedding e.symm.isClosedEmbedding

omit [IsAlgClosed k] in
/-- A nonzero homogeneous-coordinate vector defines a closed point of
polynomial projective space. Algebraic closure is not needed. -/
theorem homogeneousCoordinatePoint_isClosed (a : ι → k) (ha : a ≠ 0) :
    IsClosed ({homogeneousCoordinatePoint a ha} :
      Set (ProjectiveSpectrum 𝒜)) := by
  have inst : JacobsonSpace (AlgebraicGeometry.Proj 𝒜) :=
    polynomialProj_jacobsonSpace
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    simp only [not_exists, not_not] at h
    exact h i
  have hx : IsClosed ({affineCoordinatePoint a i} :
      Set (PrimeSpectrum (MvPolynomial {j : ι // j ≠ i} k))) := by
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    change (RingHom.ker (MvPolynomial.aeval
      (normalizedCoordinates a i)).toRingHom).IsMaximal
    exact RingHom.ker_isMaximal_of_surjective _
      (fun z ↦ ⟨MvPolynomial.C z, by simp⟩)
  have hmap :=
    (standardCoordinateChartMap k ι i).closePoints_subset_preimage_closedPoints hx
  change IsClosed ({(standardCoordinateChartMap k ι i)
    (affineCoordinatePoint a i)} : Set (ProjectiveSpectrum 𝒜)) at hmap
  rw [standardCoordinateChartMap_affineCoordinatePoint a ha i hi] at hmap
  exact hmap

omit [IsAlgClosed k] in
/-- The homogeneous-coordinate map, regarded as a map into closed points. -/
@[expose] noncomputable def projectivizationToClosedPoint :
    Projectivization k (ι → k) →
      closedPoints (AlgebraicGeometry.Proj 𝒜) :=
  fun x ↦ ⟨projectivizationToProj x, by
    induction x using Projectivization.ind with
    | h a ha => exact homogeneousCoordinatePoint_isClosed a ha⟩

omit [IsAlgClosed k] in
@[simp]
theorem projectivizationToClosedPoint_val (x : Projectivization k (ι → k)) :
    (projectivizationToClosedPoint x).1 = projectivizationToProj x :=
  rfl

omit [IsAlgClosed k] [Fintype ι] in
private theorem normalizedCoordinates_eq_of_affineCoordinatePoint_eq
    (a b : ι → k) (i : ι)
    (h : affineCoordinatePoint a i = affineCoordinatePoint b i) :
    normalizedCoordinates a i = normalizedCoordinates b i := by
  funext j
  have hj : MvPolynomial.X j - MvPolynomial.C (normalizedCoordinates a i j) ∈
      (affineCoordinatePoint a i).asIdeal := by
    change MvPolynomial.aeval (normalizedCoordinates a i)
      (MvPolynomial.X j - MvPolynomial.C (normalizedCoordinates a i j)) = 0
    simp
  rw [h] at hj
  change MvPolynomial.aeval (normalizedCoordinates b i)
    (MvPolynomial.X j - MvPolynomial.C (normalizedCoordinates a i j)) = 0 at hj
  have hba : normalizedCoordinates b i j - normalizedCoordinates a i j = 0 := by
    simpa using hj
  exact (sub_eq_zero.mp hba).symm

omit [IsAlgClosed k] in
/-- The map from vector-space projectivization to polynomial `Proj` is
injective. Algebraic closure is not needed. -/
theorem projectivizationToProj_injective :
    Function.Injective (projectivizationToProj (k := k) (ι := ι)) := by
  intro x y hxy
  induction x using Projectivization.ind with
  | h a ha =>
    induction y using Projectivization.ind with
    | h b hb =>
      change homogeneousCoordinatePoint a ha = homogeneousCoordinatePoint b hb at hxy
      obtain ⟨i, hbi⟩ : ∃ i, b i ≠ 0 := by
        by_contra h
        apply hb
        funext i
        simp only [not_exists, not_not] at h
        exact h i
      have hai : a i ≠ 0 := by
        rw [← homogeneousCoordinatePoint_mem_basicOpen_X_iff a ha i,
          hxy, homogeneousCoordinatePoint_mem_basicOpen_X_iff b hb i]
        exact hbi
      have hchart : affineCoordinatePoint a i = affineCoordinatePoint b i := by
        apply (standardCoordinateChartMap k ι i).isOpenEmbedding.injective
        rw [standardCoordinateChartMap_affineCoordinatePoint a ha i hai,
          standardCoordinateChartMap_affineCoordinatePoint b hb i hbi, hxy]
      have hnorm := normalizedCoordinates_eq_of_affineCoordinatePoint_eq a b i hchart
      rw [Projectivization.mk_eq_mk_iff' k]
      refine ⟨a i / b i, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        simp [hbi]
      · have hj := congrFun hnorm ⟨j, hji⟩
        change a j / a i = b j / b i at hj
        change (a i / b i) * b j = a j
        field_simp at hj ⊢
        exact hj.symm

/-- Over an algebraically closed field, every closed point of finite-coordinate
polynomial projective space is represented by homogeneous coordinates. -/
theorem projectivizationToProj_surjective_on_closedPoint
    (p : ProjectiveSpectrum 𝒜) (hp : IsClosed ({p} : Set (ProjectiveSpectrum 𝒜))) :
    ∃ x : Projectivization k (ι → k), projectivizationToProj x = p := by
  classical
  obtain ⟨i, hpOpen⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_X_eq_top k ι).ge (Set.mem_univ p))
  have inst : AlgebraicGeometry.IsOpenImmersion (standardCoordinateChartMap k ι i) :=
    standardCoordinateChartMap_isOpenImmersion k ι i
  have hpRange : p ∈ (standardCoordinateChartMap k ι i).opensRange := by
    rw [standardCoordinateChartMap_opensRange]
    exact hpOpen
  obtain ⟨q, hq⟩ := Scheme.Hom.mem_opensRange.mp hpRange
  have hqClosed : IsClosed ({q} :
      Set (PrimeSpectrum (MvPolynomial {j : ι // j ≠ i} k))) := by
    have hpre := hp.preimage (standardCoordinateChartMap k ι i).continuous
    have hpre_eq : (standardCoordinateChartMap k ι i) ⁻¹' ({p} :
        Set (ProjectiveSpectrum 𝒜)) = {q} := by
      ext z
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hz ↦ (standardCoordinateChartMap k ι i).isOpenEmbedding.injective
        (hz.trans hq.symm), fun hz ↦ hz ▸ hq⟩
    rw [hpre_eq] at hpre
    exact hpre
  have hqMax : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqClosed
  obtain ⟨z, hz⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hqMax
  let a : ι → k := fun j ↦ if hji : j = i then 1 else z ⟨j, hji⟩
  have hai : a i ≠ 0 := by simp [a]
  have ha : a ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [a] at hi
  have hai_one : a i = 1 := by simp [a]
  have hnorm : normalizedCoordinates a i = z := by
    funext j
    change a j.1 / a i = z j
    rw [hai_one, div_one]
    simp only [a, dite_eq_right j.2]
  have haffine : affineCoordinatePoint a i = q := by
    apply PrimeSpectrum.ext
    rw [hz]
    ext F
    change MvPolynomial.aeval (normalizedCoordinates a i) F = 0 ↔
      F ∈ MvPolynomial.vanishingIdeal k {z}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, hnorm]
  refine ⟨Projectivization.mk k a ha, ?_⟩
  rw [projectivizationToProj_mk]
  rw [← standardCoordinateChartMap_affineCoordinatePoint a ha i hai,
    haffine, hq]

/-- Over an algebraically closed field, vector-space projectivization is
equivalent to the closed points of finite-coordinate polynomial `Proj`. -/
@[expose] noncomputable def projectivizationEquivClosedPoints :
    Projectivization k (ι → k) ≃
      closedPoints (AlgebraicGeometry.Proj 𝒜) :=
  Equiv.ofBijective projectivizationToClosedPoint
    ⟨fun x y h ↦ projectivizationToProj_injective (congrArg Subtype.val h),
      fun p ↦ by
        obtain ⟨x, hx⟩ := projectivizationToProj_surjective_on_closedPoint p.1 p.2
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem projectivizationEquivClosedPoints_apply (x : Projectivization k (ι → k)) :
    (projectivizationEquivClosedPoints x).1 = projectivizationToProj x :=
  rfl

end ProjectiveSpace
