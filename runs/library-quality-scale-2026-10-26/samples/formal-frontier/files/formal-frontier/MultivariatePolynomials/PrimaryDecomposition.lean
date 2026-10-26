/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Primary

/-!
# Primary families under coefficient extension

Over a commutative ring, extension along `MvPolynomial.C` preserves and reflects a
supplied intersection of primary ideals. Deletion irredundance is preserved and
reflected over any commutative semiring. Families may be infinite; for finite index
types the two conditions give the usual primary decomposition condition, without
any assertion of existence, uniqueness, or distinct radicals.

Deletion means omitting exactly one index. Empty intersections are top; primary
and irredundance clauses for an empty family are vacuous. The variable type may
also be empty. We use the primary-ideal equivalence from
`MultivariatePolynomials.Primary` and its coefficient-ideal API.

## References

* `MultivariatePolynomials.CoefficientIdeal` supplies preservation of arbitrary
  intersections and reflection of inclusion and equality along `C`.
* `MultivariatePolynomials.Primary` supplies the equivalence for Mathlib's
  `Ideal.IsPrimary` and credits the primary-ideal formalizations it builds on.

The proofs below only combine these APIs; they do not construct decompositions.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {ι : Sort w}

/-- Transport a supplied primary-family intersection along coefficient extension. -/
theorem primary_family_map_C_iff [CommRing R] (I : Ideal R) (Q : ι → Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R) = (⨅ i, (Q i).map C) ∧
      ∀ i, ((Q i).map (C : R →+* MvPolynomial σ R)).IsPrimary) ↔
    (I = (⨅ i, Q i) ∧ ∀ i, (Q i).IsPrimary) := by
  simp only [← map_C_iInf, (map_C_injective (σ := σ)).eq_iff, isPrimary_map_C_iff]

/-- Transport deletion irredundance, with no primary or finiteness assumptions. -/
theorem irredundant_iInf_map_C_iff [CommSemiring R] (Q : ι → Ideal R) :
    (∀ i : ι, ¬ ((⨅ j : {j : ι // j ≠ i},
      (Q j.val).map (C : R →+* MvPolynomial σ R)) ≤ (Q i).map C)) ↔
    ∀ i : ι, ¬ ((⨅ j : {j : ι // j ≠ i}, Q j.val) ≤ Q i) := by
  simp only [← map_C_iInf, map_C_le_map_C_iff]

end MvPolynomial
