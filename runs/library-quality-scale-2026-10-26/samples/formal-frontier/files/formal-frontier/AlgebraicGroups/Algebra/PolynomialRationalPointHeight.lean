/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Height of a rational point of affine space

For a field and a finite set of variables, the kernel of evaluation at any
rational point has height equal to the number of variables. This includes
affine space of dimension zero. The field and index type may live in different
universes; no decidable equality on the index type is required.

The proof inducts on the finite variable type, as in mathlib's finite-variable
polynomial-dimension proof. Renaming handles equivalent variable types, and the
empty-variable polynomial-ring equivalence handles the base case; adjoining
one variable uses mathlib's
`MvPolynomial.optionEquivLeft` and `Polynomial.height_eq_height_add_one` for
the maximal evaluation ideal.

## References

* The Stacks Project, [Lemma 10.114.1](https://stacks.math.columbia.edu/tag/00OP),
  for the height of maximal ideals of a polynomial ring over a field. Its proof
  differs from the induction used here.
* The mathlib community, *Mathlib*,
  `Mathlib.RingTheory.KrullDimension.Polynomial` for the univariate height step
  and finite-variable dimension induction, `Mathlib.RingTheory.KrullDimension.Field`
  for field dimension, and `Mathlib.Algebra.MvPolynomial.Equiv` and
  `Mathlib.Algebra.MvPolynomial.Rename` for the polynomial-ring equivalences.
-/

public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

private theorem height_ker_eval_finite (K : Type u) [Field K] (σ : Type v)
    [Finite σ] (a : σ → K) :
    (RingHom.ker (eval a)).height = (Nat.card σ : ℕ∞) := by
  classical
  revert a
  induction σ using Finite.induction_empty_option with
  | of_equiv e IH =>
    intro a
    let b := a ∘ e
    let equiv := renameEquiv K e
    have he : (RingHom.ker (eval a)).comap equiv.toRingHom =
        RingHom.ker (eval b) := by
      ext p
      simp [b, equiv, Ideal.mem_comap, RingHom.mem_ker, renameEquiv_apply, eval_rename]
    calc
      (RingHom.ker (eval a)).height = ((RingHom.ker (eval a)).comap equiv.toRingHom).height :=
        (equiv.toRingEquiv.height_comap _).symm
      _ = (Nat.card _ : ℕ∞) := by rw [he, IH b, Nat.card_congr e]
  | h_empty =>
    intro a
    have hmax : (RingHom.ker (eval a)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun k => ⟨C k, eval_C k⟩)
    have hle := Ideal.height_le_ringKrullDim_of_ne_top hmax.ne_top
    rw [ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv K _),
      ringKrullDim_eq_zero_of_field] at hle
    have hz : (RingHom.ker (eval a)).height = 0 :=
      le_antisymm (WithBot.coe_le_coe.mp hle) bot_le
    simpa [Nat.card_eq_fintype_card] using hz
  | @h_option α _ IH =>
    intro a
    let old : α → K := fun index => a (some index)
    let y : K := a none
    let equiv := optionEquivLeft K α
    let evalHom := Polynomial.eval₂RingHom (eval old) y
    have he : (RingHom.ker (eval a)).comap equiv.symm.toRingHom =
        RingHom.ker evalHom := by
      ext p
      change eval a (equiv.symm p) = 0 ↔ evalHom p = 0
      have h := optionEquivLeft_elim_eval K _ old y (equiv.symm p)
      have ha : (fun x : Option α => x.elim y old) = a := by
        funext index
        cases index <;> rfl
      rw [ha, equiv.apply_symm_apply] at h
      have hh : eval a (equiv.symm p) = evalHom p := by
        simpa only [evalHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map] using h
      rw [hh]
    have hmax : (RingHom.ker evalHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun k =>
        ⟨Polynomial.C (C k), by simp [evalHom]⟩)
    have hover : (RingHom.ker evalHom).LiesOver (RingHom.ker (eval old)) := by
      constructor
      ext p
      simp [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, evalHom]
    calc
      (RingHom.ker (eval a)).height =
          ((RingHom.ker (eval a)).comap equiv.symm.toRingHom).height :=
        (equiv.symm.toRingEquiv.height_comap _).symm
      _ = (RingHom.ker evalHom).height := by rw [he]
      _ = (RingHom.ker (eval old)).height + 1 :=
        @Polynomial.height_eq_height_add_one _ _ _ _ _ hmax hover
      _ = (Nat.card (Option α) : ℕ∞) := by
        rw [IH old]
        simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one]

/-- A rational evaluation ideal has the full height of its finite-dimensional affine space.
This is a case of the polynomial maximal-ideal height in the Stacks Project,
Lemma 10.114.1; the proof instead uses mathlib's
`Polynomial.height_eq_height_add_one` and multivariable polynomial equivalences. -/
theorem height_ker_eval (K : Type u) [Field K] (σ : Type v) [Fintype σ]
    (a : σ → K) : (RingHom.ker (eval a)).height = (Fintype.card σ : ℕ∞) := by
  simpa only [Nat.card_eq_fintype_card] using height_ker_eval_finite K σ a

end MvPolynomial
