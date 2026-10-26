/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-!
# Regular differences of variables

The difference of two distinct polynomial variables is regular over any
commutative ring, including the zero ring. A triangular change of variables
reduces the assertion to regularity of a single variable.

## References

* Mathlib's `MvPolynomial.isRegular_X` and polynomial evaluation API.
-/

universe u v

namespace MvPolynomial

private noncomputable def shearForward {R : Type u} {σ : Type v}
    [CommRing R] (i j : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := by
  classical
  exact aeval (fun k => if k = i then X i + X j else X k)

private noncomputable def shearBackward {R : Type u} {σ : Type v}
    [CommRing R] (i j : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := by
  classical
  exact aeval (fun k => if k = i then X i - X j else X k)

private theorem shear_leftInverse {R : Type u} {σ : Type v}
    [CommRing R] {i j : σ} (hij : i ≠ j) :
    Function.LeftInverse (shearBackward (R := R) i j) (shearForward (R := R) i j) := by
  classical
  have h : (shearBackward (R := R) i j).comp (shearForward (R := R) i j) =
      AlgHom.id R (MvPolynomial σ R) := by
    apply algHom_ext
    intro k
    by_cases hki : k = i
    · subst k
      simp [shearForward, shearBackward, Ne.symm hij]
    · simp [shearForward, shearBackward, hki]
  intro p
  exact DFunLike.congr_fun h p

/-- The difference of two distinct variables is regular over every commutative ring. -/
theorem isRegular_X_sub_X {R : Type u} {σ : Type v} [CommRing R]
    {i j : σ} (hij : i ≠ j) : IsRegular (X i - X j : MvPolynomial σ R) := by
  classical
  rw [← isLeftRegular_iff_isRegular]
  intro p q hpq
  apply (shear_leftInverse (R := R) hij).injective
  apply (isRegular_X (R := R) (n := i)).1
  simpa [shearForward, hij, Ne.symm hij] using
    congrArg (shearForward (R := R) i j) hpq

end MvPolynomial
