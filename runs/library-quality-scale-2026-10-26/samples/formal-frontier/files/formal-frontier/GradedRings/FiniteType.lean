/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite type and the irrelevant ideal

This file characterizes finite type over the degree-zero piece of a naturally
graded commutative ring in terms of finite generation of its irrelevant ideal.
It also supplies a general finite homogeneous generating-set lemma for
finitely generated homogeneous ideals.
-/

public section

namespace HomogeneousIdeal

universe u v w

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable {ι : Type w} [DecidableEq ι] [AddMonoid ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

/-- A finitely generated homogeneous ideal admits a finite set of homogeneous
ideal generators. -/
theorem exists_finset_span_eq_of_fg (I : HomogeneousIdeal 𝒜) (hI : I.toIdeal.FG) :
    ∃ s : Finset A, Ideal.span (s : Set A) = I.toIdeal ∧
      ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x := by
  classical
  obtain ⟨U, hU⟩ := (Ideal.IsHomogeneous.iff_exists 𝒜 I.toIdeal).mp I.isHomogeneous
  obtain ⟨t, ht⟩ := hI
  have htU : (t : Set A) ⊆ Ideal.span
      ((fun x : SetLike.homogeneousSubmonoid 𝒜 => (x : A)) '' U) := by
    rw [← hU, ← ht]
    exact Ideal.subset_span
  obtain ⟨s, hsU, hts⟩ := Submodule.subset_span_finite_of_subset_span htU
  refine ⟨s, le_antisymm ?_ ?_, ?_⟩
  · rw [hU]
    exact Ideal.span_mono hsU
  · rw [← ht]
    exact Ideal.span_le.mpr hts
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hsU hx
    exact y.2

end HomogeneousIdeal

namespace GradedAlgebra

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If the irrelevant ideal is finitely generated, it has a finite set of
strictly positive-degree homogeneous generators. -/
theorem irrelevant_exists_finset_span_eq_of_fg
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    ∃ s : Finset A,
      Ideal.span (s : Set A) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      ∀ x ∈ s, ∃ n > 0, x ∈ 𝒜 n := by
  classical
  obtain ⟨s, hs, hhom⟩ :=
    HomogeneousIdeal.exists_finset_span_eq_of_fg 𝒜
      (HomogeneousIdeal.irrelevant 𝒜) h
  refine ⟨s.filter (· ≠ 0), ?_, ?_⟩
  · rw [Finset.coe_filter, show {x | x ∈ s ∧ x ≠ 0} = (s : Set A) \ {0} by ext x; simp]
    simpa only [Ideal.span_sdiff_singleton_zero] using hs
  · intro x hx
    have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
    obtain ⟨n, hxn⟩ := hhom x hxs
    refine ⟨n, ?_, hxn⟩
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    have hxirr : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      rw [← hs]
      exact Ideal.subset_span hxs
    have hxproj := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x).mp hxirr
    have hx0 : x = 0 := by
      simpa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hxn] using hxproj
    exact (Finset.mem_filter.mp hx).2 hx0

/-- Finite generation of the irrelevant ideal implies finite type over the
degree-zero piece. The proof uses strong induction on homogeneous degree and
does not require a domain or nontriviality assumption. -/
theorem finiteType_of_irrelevant_fg
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) A := by
  classical
  obtain ⟨s, hs, hhom⟩ := irrelevant_exists_finset_span_eq_of_fg 𝒜 h
  have hdegree : ∀ n (x : A), x ∈ 𝒜 n →
      x ∈ Algebra.adjoin (𝒜 0) (s : Set A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hxn
      by_cases hn0 : n = 0
      · subst n
        exact Subalgebra.algebraMap_mem _ (⟨x, hxn⟩ : 𝒜 0)
      · have hxirr : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
          HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (Nat.pos_of_ne_zero hn0) hxn
        rw [← hs] at hxirr
        have hproj : ∀ y ∈ Ideal.span (s : Set A),
            ((DirectSum.decompose 𝒜 y) n : A) ∈ Algebra.adjoin (𝒜 0) (s : Set A) := by
          intro y hy
          induction hy using Submodule.closure_induction with
          | zero => simp
          | add y z _ _ hy hz =>
              rw [DirectSum.decompose_add]
              exact Subalgebra.add_mem _ hy hz
          | smul_mem a y hy =>
              obtain ⟨d, hd, hyd⟩ := hhom y hy
              rw [smul_eq_mul]
              by_cases hdn : d ≤ n
              · rw [DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 hyd hdn]
                exact Subalgebra.mul_mem _
                  (ih (n - d) (Nat.sub_lt (Nat.pos_of_ne_zero hn0) hd) _
                    ((DirectSum.decompose 𝒜 a) (n - d)).2)
                  (Algebra.subset_adjoin hy)
              · rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le 𝒜 hyd hdn]
                exact Subalgebra.zero_mem _
        simpa [DirectSum.decompose_of_mem_same 𝒜 hxn] using hproj _ hxirr
  refine ⟨⟨s, ?_⟩⟩
  rw [← top_le_iff]
  intro x _
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Subalgebra.sum_mem _ fun n _ =>
    hdegree n _ ((DirectSum.decompose 𝒜 x) n).2

/-- Positive-degree homogeneous algebra generators span the irrelevant ideal
as an ideal. -/
theorem irrelevant_le_span_of_adjoin_eq_top (s : Set A)
    (hhom : ∀ x ∈ s, ∃ n ≠ 0, x ∈ 𝒜 n)
    (hgen : Algebra.adjoin (𝒜 0) s = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span s := by
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have hx : x ∈ Algebra.adjoin (𝒜 0) s := by rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨n, hn, hxn⟩ := hhom x hx
      rw [GradedRing.projZeroRingHom_apply,
        DirectSum.decompose_of_mem_ne 𝒜 hxn hn, sub_zero]
      exact Ideal.subset_span hx
  | algebraMap r =>
      convert! Ideal.zero_mem (Ideal.span s)
      rw [sub_eq_zero]
      exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y _ _ _ _ =>
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ ‹_› ‹_›
  | mul x y _ _ hx' hy' =>
      convert!
        Ideal.add_mem _ (Ideal.mul_mem_left _ x hy')
          (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
      rw [map_mul]
      ring

/-- Finite type over the degree-zero piece implies finite generation of the
irrelevant ideal. -/
theorem irrelevant_fg_of_finiteType [Algebra.FiniteType (𝒜 0) A] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG := by
  obtain ⟨s, hs, hhom⟩ :=
    GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  have hle : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (s : Set A) :=
    irrelevant_le_span_of_adjoin_eq_top 𝒜 (s : Set A) (by simpa using hhom) (by simpa using hs)
  refine ⟨s, le_antisymm ?_ hle⟩
  exact Ideal.span_le.mpr fun x hx =>
    let ⟨n, hn, hxn⟩ := hhom x hx
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (Nat.pos_of_ne_zero hn) hxn

/-- For a naturally graded commutative ring, the irrelevant ideal is finitely
generated if and only if the ring is of finite type over its degree-zero
piece. -/
theorem irrelevant_fg_iff_finiteType :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG ↔ Algebra.FiniteType (𝒜 0) A :=
  ⟨finiteType_of_irrelevant_fg 𝒜, fun _ => irrelevant_fg_of_finiteType 𝒜⟩

end GradedAlgebra
