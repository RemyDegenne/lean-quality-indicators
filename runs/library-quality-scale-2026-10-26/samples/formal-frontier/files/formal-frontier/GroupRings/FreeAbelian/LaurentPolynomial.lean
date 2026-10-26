/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Group algebras of free abelian groups

This file identifies the group algebra of a free abelian group with the
multivariable Laurent polynomial algebra.  Laurent monomials are represented by
finitely supported integer exponent vectors.
-/

@[expose] public section

open Multiplicative

universe u v w

/-- Multivariable Laurent polynomials with variables indexed by `σ` and
coefficients in `A`. -/
abbrev MvLaurentPolynomial (σ : Type u) (A : Type v) [Semiring A] :=
  AddMonoidAlgebra A (σ →₀ ℤ)

namespace AddEquiv

variable {A : Type u} {G : Type v} {σ : Type w} [CommSemiring A] [AddCommGroup G]

/-- Additive coordinates on a group induce an algebra equivalence from its
group algebra to the corresponding multivariable Laurent polynomial algebra. -/
noncomputable def monoidAlgebraMultiplicativeEquivMvLaurentPolynomial
    (e : G ≃+ (σ →₀ ℤ)) :
    MonoidAlgebra A (Multiplicative G) ≃ₐ[A] MvLaurentPolynomial σ A :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv A A G).symm.trans
    (AddMonoidAlgebra.domCongr A A e)

/-- Supplied additive coordinates send a group-algebra basis term at `g` to the
Laurent basis term with exponent vector `e g`, preserving its coefficient. -/
@[simp]
theorem monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single
    (e : G ≃+ (σ →₀ ℤ)) (g : G) (a : A) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial
        (MonoidAlgebra.single (.ofAdd g) a) =
      AddMonoidAlgebra.single (e g) a := by
  have h :
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv A A G).symm
          (MonoidAlgebra.single (.ofAdd g) a) =
        AddMonoidAlgebra.single g a := by
    apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv A A G).injective
    simp
  simp [monoidAlgebraMultiplicativeEquivMvLaurentPolynomial, h]

/-- The inverse coordinate equivalence sends a Laurent basis term at `m` to
the group-algebra basis term at `e.symm m`, preserving its coefficient. -/
@[simp]
theorem monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_symm_single
    (e : G ≃+ (σ →₀ ℤ)) (m : σ →₀ ℤ) (a : A) :
    e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.symm
        (AddMonoidAlgebra.single m a) =
      MonoidAlgebra.single (.ofAdd (e.symm m)) a := by
  apply e.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial.injective
  simp

end AddEquiv

namespace FreeAbelianGroup

variable (A : Type u) [CommSemiring A]

/-- The group algebra of the free abelian group on `σ` is the multivariable
Laurent polynomial algebra on `σ`. -/
noncomputable def monoidAlgebraEquivMvLaurentPolynomial (σ : Type v) :
    MonoidAlgebra A (Multiplicative (FreeAbelianGroup σ)) ≃ₐ[A]
      MvLaurentPolynomial σ A :=
  (equivFinsupp σ).monoidAlgebraMultiplicativeEquivMvLaurentPolynomial

/-- The canonical free-abelian equivalence sends a basis term at `g` to the
Laurent basis term whose exponent vector is `equivFinsupp σ g`. -/
@[simp]
theorem monoidAlgebraEquivMvLaurentPolynomial_single
    (σ : Type v) (g : FreeAbelianGroup σ) (a : A) :
    monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd g) a) =
      AddMonoidAlgebra.single (equivFinsupp σ g) a := by
  exact AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_single
    (equivFinsupp σ) g a

/-- The inverse canonical equivalence sends a Laurent basis term at `m` to the
free-abelian group element with coordinates `m`, preserving its coefficient. -/
@[simp]
theorem monoidAlgebraEquivMvLaurentPolynomial_symm_single
    (σ : Type v) (m : σ →₀ ℤ) (a : A) :
    (monoidAlgebraEquivMvLaurentPolynomial A σ).symm
        (AddMonoidAlgebra.single m a) =
      MonoidAlgebra.single (.ofAdd ((equivFinsupp σ).symm m)) a := by
  exact AddEquiv.monoidAlgebraMultiplicativeEquivMvLaurentPolynomial_symm_single
    (equivFinsupp σ) m a

/-- A basis term at the free generator `of i` has exponent one at `i` and zero
elsewhere. Its coefficient is unchanged. The specialized simp rule has priority
1100, before the general single-term rules. -/
@[simp 1100]
theorem monoidAlgebraEquivMvLaurentPolynomial_generator
    (σ : Type v) (i : σ) (a : A) :
    monoidAlgebraEquivMvLaurentPolynomial A σ
        (MonoidAlgebra.single (.ofAdd (of i)) a) =
      AddMonoidAlgebra.single (Finsupp.single i 1) a := by
  rw [monoidAlgebraEquivMvLaurentPolynomial_single]
  simp

end FreeAbelianGroup
