/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import ToricIdeals.RationalNormalCurve.Injectivity

/-!
# Freeness over the rational-normal-curve source

The full bivariate polynomial semiring `Target R` is a module over the full
polynomial source `Source R n` through the monomial parametrization `rncMap R n`.
Its scalar action is `p • q = rncMap R n p * q`. This module is free exactly
when `n = 1` or the coefficient semiring is subsingleton, for every commutative
semiring in every universe and every natural-number degree.

Here `Module.Free` means existence of a basis with an arbitrary index type,
not necessarily a finite basis. Over nontrivial coefficients, the target is
nontrivial; Mathlib's free-module faithfulness theorem then makes the raw map
injective. The injectivity criterion excludes degree zero and degrees at least
two. In degree one the map is the identity and the action is multiplication,
giving the singleton basis. Subsingleton coefficients give zero polynomial
carriers and the empty basis.

This concerns neither the coefficient action on the target nor the coefficient
module of the Hankel quotient. In degree zero the source remains the full
one-variable polynomial semiring, whose variable maps to `1`. No quotient or
parametrization-image carrier is substituted. The module argument is explicit
so that even in degree one, when the source and target carriers coincide, its
action is fixed by the raw map rather than by instance priority.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Injectivity`, for the
  all-degree injectivity criterion on the full source over commutative semirings.
* Mathlib contributors, `Mathlib.LinearAlgebra.FreeModule.Basic` and
  `Mathlib.Algebra.Algebra.Basic`, for free-module faithfulness, singleton and
  empty bases, and the injectivity of the algebra map of a faithful algebra.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

universe u

private theorem rncMap_one_module_eq_self (R : Type u) [CommSemiring R] :
    @Algebra.toModule (Source R 1) (Target R) inferInstance inferInstance
      (rncMap R 1).toAlgebra = (inferInstance : Module (Target R) (Target R)) := by
  apply Module.ext'
  intro p q
  calc
    _ = rncMap R 1 p * q := RingHom.smul_toAlgebra (rncMap R 1) p q
    _ = p * q := by rw [rncMap_one]; rfl

/-- The full bivariate polynomial semiring is free over the full polynomial source,
with the module structure induced by the rational-normal-curve monomial map,
exactly in degree one or over a subsingleton coefficient semiring.

This is arbitrary-basis freeness over commutative semirings, in every universe
and every degree, including zero. The explicit module argument fixes the scalar
action as `p • q = rncMap R n p * q`, not the coefficient action. -/
theorem rncMap_moduleFree_iff (R : Type u) [CommSemiring R] (n : ℕ) :
    @Module.Free (Source R n) (Target R) inferInstance inferInstance
      (@Algebra.toModule (Source R n) (Target R) inferInstance inferInstance
        (rncMap R n).toAlgebra) ↔ n = 1 ∨ Subsingleton R := by
  constructor
  · intro hfree
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · let : Nontrivial R := hR
      let : Algebra (Source R n) (Target R) := (rncMap R n).toAlgebra
      let : Module (Source R n) (Target R) :=
        @Algebra.toModule (Source R n) (Target R) inferInstance inferInstance
          (rncMap R n).toAlgebra
      let : Module.Free (Source R n) (Target R) := hfree
      let : Nontrivial (Target R) := MvPolynomial.nontrivial_of_nontrivial (Fin 2) R
      let : FaithfulSMul (Source R n) (Target R) :=
        Module.Free.instFaithfulSMulOfNontrivial _ _
      have hinj : Function.Injective (rncMap R n) := by
        simpa only [RingHom.algebraMap_toAlgebra] using
          (FaithfulSMul.algebraMap_injective (Source R n) (Target R))
      exact (rncMap_injective_iff R n).mp hinj
  · rintro (rfl | hR)
    · rw [rncMap_one_module_eq_self]
      exact Module.Free.self _
    · let : Subsingleton R := hR
      let : Module (Source R n) (Target R) :=
        @Algebra.toModule (Source R n) (Target R) inferInstance inferInstance
          (rncMap R n).toAlgebra
      exact Module.Free.of_subsingleton (Source R n) (Target R)

end ToricIdeals.RationalNormalCurve
