/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact sequences and exact functors for additive Euler invariants

Finite signed term sums respect short exact sequences of complexes in every interval,
including empty intervals. With termwise support bounds, the same holds for homology
sums. An exact functor transports an additive invariant, termwise support, and the
native homology comparison isomorphism; no homological boundedness assumption is used.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v u' v' w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Γ : Type w} [AddCommGroup Γ]
variable (μ : C → Γ)
variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

/-- Degreewise short exactness makes the finite signed term sum additive,
without any support or nonempty-interval assumption. -/
theorem term_sum_additive_of_shortExact (S : ShortComplex (ChainComplex C ℤ))
    (hS : S.ShortExact) (a b : ℤ) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (S.X₂.X j)) =
      (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (S.X₁.X j)) +
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (S.X₃.X j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj := hμ (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) j))
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS j)
  change μ (S.X₂.X j) = μ (S.X₁.X j) + μ (S.X₃.X j) at hj
  rw [hj, smul_add]

/-- Bounded homology Euler sums inherit additivity from degreewise exact terms. -/
theorem homology_sum_additive_of_shortExact (S : ShortComplex (ChainComplex C ℤ))
    (hS : S.ShortExact) (a b : ℤ) (hab : a ≤ b)
    (h₁ : ∀ j, j < a ∨ b < j → IsZero (S.X₁.X j))
    (h₂ : ∀ j, j < a ∨ b < j → IsZero (S.X₂.X j))
    (h₃ : ∀ j, j < a ∨ b < j → IsZero (S.X₃.X j)) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (S.X₂.homology j)) =
      (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (S.X₁.homology j)) +
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (S.X₃.homology j) := by
  rw [← euler_eq_homology_of_bounded μ hμ S.X₁ a b hab h₁,
    ← euler_eq_homology_of_bounded μ hμ S.X₂ a b hab h₂,
    ← euler_eq_homology_of_bounded μ hμ S.X₃ a b hab h₃]
  exact term_sum_additive_of_shortExact μ hμ S hS a b

omit hμ

variable {D : Type u'} [Category.{v'} D] [Abelian D]

section Support

variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Termwise support survives a zero-morphism-preserving functor. -/
theorem map_termwise_bounded (K : ChainComplex C ℤ) (a b : ℤ)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j)) :
    ∀ j, j < a ∨ b < j →
      IsZero (((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).X j) := by
  intro j hj
  exact F.map_isZero (hK j hj)

end Support

variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (ν : D → Γ)
variable (hν : ∀ S : ShortComplex D, S.ShortExact → ν S.X₂ = ν S.X₁ + ν S.X₃)

include hν

/-- The invariant obtained by precomposing with an exact functor remains SES-additive. -/
theorem precompose_exact_ses (S : ShortComplex C) (hS : S.ShortExact) :
    ν (F.obj S.X₂) = ν (F.obj S.X₁) + ν (F.obj S.X₃) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃] using
    hν (S.map F) (hS.map_of_exact F)

omit hν

/-- The native homology comparison for a degreewise mapped chain complex. -/
def map_homology_iso (K : ChainComplex C ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).homology i ≅
      F.obj (K.homology i) := by
  exact (K.sc i).mapHomologyIso F

include hν

/-- Exact functors preserve additive homology values through the native comparison. -/
theorem invariant_map_homology (K : ChainComplex C ℤ) (i : ℤ) :
    ν (((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).homology i) =
      ν (F.obj (K.homology i)) :=
  invariant_iso ν hν (map_homology_iso F K i)

/-- Homology-sum compatibility requires no termwise support bounds. -/
theorem homology_sum_map (K : ChainComplex C ℤ) (a b : ℤ) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) •
      ν (((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).homology j)) =
      ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • ν (F.obj (K.homology j)) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [invariant_map_homology F ν hν K j]

/-- On a common term-support interval, the mapped term Euler sum equals both
the mapped homology sum and the original homology sum evaluated after `F`. -/
theorem euler_map_bounded (K : ChainComplex C ℤ) (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j)) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • ν (F.obj (K.X j))) =
      (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) •
        ν (((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).homology j)) ∧
      (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • ν (F.obj (K.X j))) =
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • ν (F.obj (K.homology j)) := by
  constructor
  · change (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) •
        ν (((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).X j)) = _
    exact euler_eq_homology_of_bounded ν hν _ a b hab
      (map_termwise_bounded F K a b hK)
  · exact euler_eq_homology_of_bounded (fun X => ν (F.obj X))
      (precompose_exact_ses F ν hν) K a b hab hK

end CategoryTheory.AdditiveEuler
