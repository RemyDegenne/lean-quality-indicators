/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Noetherian

/-!
# Noetherianity and the irrelevant ideal

This file characterizes Noetherian naturally graded commutative rings using
Noetherianity of the degree-zero piece and finite generation of the irrelevant
ideal.
-/

public section

namespace GradedAlgebra

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A Noetherian naturally graded ring has finitely generated irrelevant
ideal. -/
theorem irrelevant_fg_of_isNoetherianRing [IsNoetherianRing A] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG :=
  Ideal.fg_of_isNoetherianRing _

/-- If the degree-zero piece is Noetherian and the irrelevant ideal is
finitely generated, then the whole naturally graded ring is Noetherian. -/
theorem isNoetherianRing_of_gradeZero_of_irrelevant_fg
    [IsNoetherianRing (𝒜 0)]
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    IsNoetherianRing A := by
  let _ : Algebra.FiniteType (𝒜 0) A := finiteType_of_irrelevant_fg 𝒜 h
  exact Algebra.FiniteType.isNoetherianRing (𝒜 0) A

/-- A naturally graded commutative ring is Noetherian exactly when its
degree-zero piece is Noetherian and its irrelevant ideal is finitely
generated. -/
theorem isNoetherianRing_iff_gradeZero_and_irrelevant_fg :
    IsNoetherianRing A ↔
      IsNoetherianRing (𝒜 0) ∧
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG := by
  constructor
  · intro hA
    let _ : IsNoetherianRing A := hA
    exact ⟨inferInstance, irrelevant_fg_of_isNoetherianRing 𝒜⟩
  · rintro ⟨h0, hfg⟩
    let _ : IsNoetherianRing (𝒜 0) := h0
    exact isNoetherianRing_of_gradeZero_of_irrelevant_fg 𝒜 hfg

end GradedAlgebra
