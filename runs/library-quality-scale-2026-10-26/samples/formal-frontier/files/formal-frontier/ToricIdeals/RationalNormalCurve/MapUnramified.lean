/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.RingHom.Unramified
public import ToricIdeals.RationalNormalCurve.MapSurjectivity

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Formal unramifiedness of the rational-normal-curve parametrization

For a commutative ring `R`, the polynomial parametrization `rncMap R n` is
formally unramified exactly when `n = 1` or `R` is subsingleton.

The map has source `Source R n = MvPolynomial (Fin (n + 1)) R` and target
`Target R = MvPolynomial (Fin 2) R`. It preserves coefficients by `rncMap_C`
and sends each source variable to its designated monomial by `rncMap_X`.
Here `RingHom.FormallyUnramified` uses the source polynomial ring as the base:
the algebra structure on the target is `(rncMap R n).toAlgebra`. This is not
formal unramifiedness over the coefficient ring, nor a property of the image
or of a Hankel quotient.

At degree zero the source is still `R[X₀]`, and the sole variable maps to `1`.
It is not replaced by `R` or sent to `0`. At degree one `rncMap_one` identifies
the parametrization with the identity on the bivariate polynomial ring.
Subsingleton coefficient rings are included in every degree.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the source,
  target and coefficient, variable and degree-one APIs of the parametrization.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.MapSurjectivity`,
  for the surjectivity classification of the same polynomial map.
* Mathlib contributors, `Mathlib.RingTheory.RingHom.Unramified`, for formal
  unramifiedness of a ring homomorphism and its surjective case.
* Mathlib contributors, `Mathlib.Algebra.DualNumber` and
  `Mathlib.Algebra.TrivSqZeroExt.Ideal`, for the dual-number evaluations and
  square-zero projection kernel used in the converse.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

noncomputable section

universe u

private theorem not_formallyUnramified_rncMap (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 1) : ¬ RingHom.FormallyUnramified (rncMap R n) := by
  classical
  let c : R →+* DualNumber R := TrivSqZeroExt.inlHom R R
  let eε : Target R →+* DualNumber R :=
    MvPolynomial.eval₂Hom c (fun j => if j = 0 then DualNumber.eps else 0)
  let e₀ : Target R →+* DualNumber R := MvPolynomial.eval₂Hom c (fun _ => 0)
  have heps : (DualNumber.eps : DualNumber R) ^ n = (0 : DualNumber R) ^ n := by
    by_cases hn0 : n = 0
    · simp [hn0]
    · have htwo : 2 ≤ n := by omega
      rw [pow_eq_zero_of_le htwo (DualNumber.eps_pow_two (R := R)), zero_pow hn0]
  have heval (v : Fin 2 → DualNumber R) (i : Fin (n + 1)) :
      MvPolynomial.eval₂Hom c v (MvPolynomial.monomial (coordinateExponent n i) 1) =
        v 0 ^ (n - i.val) * v 1 ^ i.val := by
    simp only [MvPolynomial.eval₂Hom_monomial, map_one, one_mul]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp [coordinateExponent]
  -- At degree zero both evaluations of the sole source variable are 1.
  -- Establish the common source-base map before making either evaluation an algebra map.
  have hbase : eε.comp (rncMap R n) = e₀.comp (rncMap R n) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [eε, e₀]
    · intro i
      simp only [RingHom.comp_apply, rncMap_X, eε, e₀]
      rw [heval, heval]
      by_cases hi : i.val = 0
      · simpa [hi] using heps
      · simp [hi]
  let ρ : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom
  have hproj : ρ.comp eε = ρ.comp e₀ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [eε, e₀, ρ]
    · intro i
      by_cases hi : i = 0 <;> simp [eε, e₀, ρ, hi]
  have hnil : IsNilpotent (RingHom.ker ρ) := by
    exact ⟨2, TrivSqZeroExt.kerIdeal_sq R R⟩
  intro h
  letI : Algebra (Source R n) (Target R) := (rncMap R n).toAlgebra
  letI : Algebra (Source R n) (DualNumber R) := (e₀.comp (rncMap R n)).toAlgebra
  let gε : Target R →ₐ[Source R n] DualNumber R :=
    { toRingHom := eε
      commutes' := fun x => RingHom.congr_fun hbase x }
  let g₀ : Target R →ₐ[Source R n] DualNumber R :=
    { toRingHom := e₀
      commutes' := fun _ => rfl }
  letI : Algebra.FormallyUnramified (Source R n) (Target R) := h
  have hg : gε = g₀ :=
    Algebra.FormallyUnramified.lift_unique_of_ringHom ρ hnil gε g₀ hproj
  have heq := AlgHom.congr_fun hg (MvPolynomial.X (0 : Fin 2))
  have h10 : (1 : R) = 0 := by
    simpa [gε, g₀, eε, e₀] using congrArg TrivSqZeroExt.snd heq
  exact one_ne_zero h10

/-- The rational-normal-curve polynomial parametrization is formally unramified,
with its source polynomial ring as base, precisely in degree one or over a
subsingleton coefficient ring. This includes degree zero and arbitrary
commutative coefficient rings in every universe. -/
theorem rncMap_formallyUnramified_iff (R : Type u) [CommRing R] (n : ℕ) :
    RingHom.FormallyUnramified (rncMap R n) ↔ n = 1 ∨ Subsingleton R := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · letI : Nontrivial R := hR
      left
      by_contra hn
      exact not_formallyUnramified_rncMap R n hn h
  · intro h
    exact RingHom.FormallyUnramified.of_surjective ((rncMap_surjective_iff R n).mpr h)

end

end ToricIdeals.RationalNormalCurve
