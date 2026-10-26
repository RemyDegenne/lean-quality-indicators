/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic

/-!
# Dimensions of homogeneous polynomial spaces

This file computes the finrank of the degree-`d` homogeneous component of a
multivariable polynomial ring over a commutative semiring satisfying the strong
rank condition. Its monomial basis is indexed by weak compositions of `d`, so
the finrank is a multichoose number. The specialization to `n + 1` variables
gives the familiar binomial coefficient `(n + d).choose d`.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommSemiring R] [StrongRankCondition R]

/-- The degree-`d` homogeneous polynomials in finitely many variables have one
basis vector for every weak composition of `d`. -/
theorem finrank_homogeneousSubmodule (σ : Type v) [Fintype σ] (d : ℕ) :
    Module.finrank R (homogeneousSubmodule σ R d) =
      (Fintype.card σ).multichoose d := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  let S : Set (σ →₀ ℕ) := {m | m.degree = d}
  let A : Finset (σ →₀ ℕ) := Finset.univ.finsuppAntidiag d
  have hS : S = (A : Set (σ →₀ ℕ)) := by
    ext m
    simp [S, A, Finsupp.degree_eq_sum]
  let _ : Fintype S := Set.Finite.fintype (hS ▸ A.finite_toSet)
  calc
    Module.finrank R (AddMonoidAlgebra.supported R R S) =
        Module.finrank R (S →₀ R) :=
      LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp S)
    _ = Fintype.card S := Module.finrank_finsupp_self R
    _ = Fintype.card A := Fintype.card_congr (Set.equivOfEq hS)
    _ = A.card := Fintype.card_coe A
    _ = (Fintype.card σ).multichoose d := by
      simpa [A] using
        (Finset.card_finsuppAntidiag_nat_eq_multichoose (s := Finset.univ) d)

/-- In `n + 1` variables, the degree-`d` homogeneous polynomials have
dimension `(n + d).choose d`. -/
theorem finrank_homogeneousSubmodule_fin (n d : ℕ) :
    Module.finrank R (homogeneousSubmodule (Fin (n + 1)) R d) =
      (n + d).choose d := by
  rw [finrank_homogeneousSubmodule, Nat.multichoose_eq, Fintype.card_fin]
  congr 1
  omega

end ProjectiveSpace
