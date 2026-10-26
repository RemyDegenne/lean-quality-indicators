/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Logic.Function.Basic

/-!
# Injectivity and recovery for finite coefficient sums

`Finsupp.mapDomain` groups a finitely supported coefficient family by an index map,
adding the coefficients with the same image. Its injectivity is equivalent to
injectivity of the index map or subsingleton coefficients.

For bivariate monomial exponents, grouping coefficients by both total degree and
the number of variables with positive exponent admits a total recovery map exactly
when the coefficient monoid is subsingleton. The recovery map is not required to
preserve any algebraic operations.

## References

* Mathlib, `Mathlib.Data.Finsupp.Basic`: `Finsupp.mapDomain`, its action on
  singleton coefficient families, and injectivity for injective index maps.
* Mathlib, `Mathlib.Data.Finsupp.Single`: injectivity of singleton coefficient
  families in their index when the coefficient is nonzero.
* Mathlib, `Mathlib.Data.Finsupp.Defs`: subsingleton finitely supported functions.
* Mathlib, `Mathlib.Data.Finsupp.Weight`: total degree of monomial exponents.
* Mathlib, `Mathlib.Logic.Function.Basic`: injectivity on subsingleton domains
  and the equivalence between injectivity and existence of a left inverse.
-/

@[expose] public section

universe u v w

namespace Finsupp

/-- Reindexing and adding a finitely supported coefficient family is injective
exactly when the index map is injective or the coefficient monoid is subsingleton.
This sharpens `Finsupp.mapDomain_injective` by including the degenerate coefficient
case. Only an additive commutative monoid is needed; cancellation is not required. -/
theorem mapDomain_injective_iff {α : Type u} {β : Type v} {M : Type w}
    [AddCommMonoid M] (f : α → β) :
    Function.Injective (Finsupp.mapDomain f : (α →₀ M) → (β →₀ M)) ↔
      Function.Injective f ∨ Subsingleton M := by
  classical
  constructor
  · intro h
    by_cases hM : Subsingleton M
    · exact Or.inr hM
    · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
      obtain ⟨c, hc⟩ := exists_ne (0 : M)
      left
      intro a b hab
      apply single_left_injective hc
      apply h
      simp only [mapDomain_single, hab]
  · rintro (hf | hM)
    · exact mapDomain_injective hf
    · let : Subsingleton M := hM
      exact Function.injective_of_subsingleton _

/-- Grouping bivariate monomial coefficients by total degree and the number of
variables with positive exponent admits a total recovery map exactly when the
coefficient monoid is subsingleton. This excludes every total recovery function
for nonsubsingleton coefficients, not just additive or multiplicative ones.

The distinct exponent vectors `Finsupp.single (0 : Fin 2) 1` and
`Finsupp.single (1 : Fin 2) 1` both have degree one and support cardinality one,
so these two statistics do not distinguish the two variables. -/
theorem mapDomain_degree_support_hasLeftInverse_iff (M : Type w) [AddCommMonoid M] :
    Function.HasLeftInverse
        (Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) :
          ((Fin 2 →₀ ℕ) →₀ M) → ((ℕ × ℕ) →₀ M)) ↔
      Subsingleton M := by
  have hcollision :
      ¬ Function.Injective (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) := by
    intro h
    have hsingle :
        (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) =
          Finsupp.single (1 : Fin 2) 1 := by
      apply h
      simp only [Finsupp.degree_single,
        Finsupp.support_single (0 : Fin 2) Nat.one_ne_zero,
        Finsupp.support_single (1 : Fin 2) Nat.one_ne_zero, Finset.card_singleton]
    have hindex : (0 : Fin 2) = 1 :=
      Finsupp.single_left_injective Nat.one_ne_zero hsingle
    exact Nat.zero_ne_one (congrArg Fin.val hindex)
  rw [← Function.injective_iff_hasLeftInverse, mapDomain_injective_iff]
  simp only [hcollision, false_or]

end Finsupp
