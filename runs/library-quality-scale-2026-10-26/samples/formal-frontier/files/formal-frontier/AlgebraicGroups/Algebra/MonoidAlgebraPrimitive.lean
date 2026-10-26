/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

@[expose] public section

/-!
# Primitive elements of monoid algebras

The canonical bialgebra on a monoid algebra has no nonzero primitive elements, over
any commutative semiring and for any monoid of indices. Here primitivity includes
both the comultiplication identity and a zero counit. Over semirings without
additive cancellation, the comultiplication identity alone does not imply this
conclusion: over the Boolean semiring with the trivial monoid, `1` satisfies the
comultiplication identity but has nonzero counit.

The proof compares diagonal coefficients of the comultiplication and the two
unit tensors, then uses the counit at the identity. This generalizes the
finite cyclic group-algebra argument in the exposition cited below to
arbitrary monoids and commutative semirings.

## References

- Formal Frontier, *Alpha-power versus roots of unity: scheme isomorphism, not group
  isomorphism*, § “No group-scheme isomorphism for positive exponent” (finite
  cyclic group-algebra diagonal-coefficient argument).
- Mathlib, `Mathlib.RingTheory.Coalgebra.MonoidAlgebra`,
  `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`, and
  `Mathlib.RingTheory.Bialgebra.Primitive` (the monoid-algebra comultiplication,
  counit, and primitive-element predicate).
- Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra` (the tensor-product
  coefficient equivalence used in the diagonal argument).
-/

open scoped TensorProduct

namespace MonoidAlgebra

variable {K M : Type*} [CommSemiring K] [Monoid M]

/-- Every primitive element of the canonical bialgebra on a monoid algebra is zero.
No cancellation, nontriviality, commutativity or finiteness hypothesis on the indices
is required. The diagonal-coefficient proof extends the finite cyclic group-algebra
argument of Formal Frontier's *Alpha-power versus roots of unity: scheme isomorphism,
not group isomorphism* exposition; the counit eliminates the coefficient at the
identity over semirings. -/
theorem isPrimitiveElem_iff_eq_zero (x : MonoidAlgebra K M) :
    Bialgebra.IsPrimitiveElem K x ↔ x = 0 := by
  constructor
  · intro hx
    have hdiag (g : M) :
        ((tensorEquiv K) (Coalgebra.comul (R := K) x)).coeff (g, g) = x.coeff g := by
      calc
        _ = ((tensorEquiv K) (Coalgebra.comul (R := K) (x.coeff.sum single))).coeff
            (g, g) := by rw [x.sum_coeff_single]
        _ = x.coeff g := by
          classical
          simp only [Finsupp.sum, map_sum,
            MonoidAlgebra.comul_single, CommSemiring.comul_apply,
            TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
            MonoidAlgebra.tensorEquiv_single_tmul_single]
          simp [Finsupp.single_apply, Prod.mk.injEq, Finsupp.mem_support_iff]
          exact fun hg ↦ hg.symm
    have hleft (g : M) (hg : g ≠ 1) :
        ((tensorEquiv K) (1 ⊗ₜ[K] x)).coeff (g, g) = 0 := by
      conv_lhs => rw [← x.sum_coeff_single]
      simp [MonoidAlgebra.one_def, hg]
    have hright (g : M) (hg : g ≠ 1) :
        ((tensorEquiv K) (x ⊗ₜ[K] 1)).coeff (g, g) = 0 := by
      conv_lhs => rw [← x.sum_coeff_single]
      simp [MonoidAlgebra.one_def, hg]
    have hcoeff (g : M) (hg : g ≠ 1) : x.coeff g = 0 := by
      have h := congrArg
        (fun t : MonoidAlgebra K M ⊗[K] MonoidAlgebra K M ↦
          ((tensorEquiv K) t).coeff (g, g)) hx.comul_eq_tmul_add_tmul
      rw [map_add] at h
      change ((tensorEquiv K) (Coalgebra.comul (R := K) x)).coeff (g, g) =
        ((tensorEquiv K) (1 ⊗ₜ[K] x)).coeff (g, g) +
        ((tensorEquiv K) (x ⊗ₜ[K] 1)).coeff (g, g) at h
      rw [hdiag, hleft g hg, hright g hg, add_zero] at h
      exact h
    have hxsingle : x = single (1 : M) (x.coeff 1) := by
      ext g
      by_cases hg : g = 1
      · subst g
        simp
      · simpa [Finsupp.single_apply, hg] using hcoeff g hg
    have hzero : x.coeff 1 = 0 := by
      have hc := hx.counit_eq_zero
      rw [hxsingle, MonoidAlgebra.counit_single, CommSemiring.counit_apply] at hc
      exact hc
    rw [hxsingle, hzero, single_zero]
  · rintro rfl
    exact Coalgebra.IsSkewPrimitiveElem.zero

end MonoidAlgebra
