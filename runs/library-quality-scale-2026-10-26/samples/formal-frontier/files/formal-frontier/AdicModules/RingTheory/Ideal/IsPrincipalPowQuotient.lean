/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient

/-!
# Representatives for quotients of powers of a principal ideal

For a nonzero principal ideal `I` in a commutative domain, Mathlib's
`Ideal.quotEquivPowQuotPowSucc h h' n` sends the class of `a` modulo `I` to
that of `a * g ^ n`, where `g = h.principal.choose`. The target is the quotient
of the module `I ^ n` by `I • ⊤`. The inverse sends this representative back to
the class of `a`. Both formulas also hold for the plain equivalence
`Ideal.quotEquivPowQuotPowSuccEquiv`, including at exponent zero.

The generator is the one chosen by the supplied proof of principality; it is
not an independently specified generator of the same ideal.

## References

* Yakov Pechersky's principal-ideal power quotient equivalences in
  `Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient`. The representative formulas
  below describe these equivalences without changing their constructions.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [IsDomain R] {I : Ideal R}
  (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ)

/-- The principal-power quotient linear equivalence multiplies representatives
by the `n`th power of the generator chosen by `h`. -/
@[simp]
theorem quotEquivPowQuotPowSucc_apply_mk (a : R) :
    quotEquivPowQuotPowSucc h h' n (Quotient.mk I a) =
      Submodule.Quotient.mk
        (⟨a * h.principal.choose ^ n,
          Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
            (h.principal.choose_spec.ge (Ideal.mem_span_singleton_self _)) n)⟩ :
          (I ^ n : Ideal R)) := by
  change quotEquivPowQuotPowSucc h h' n (Submodule.Quotient.mk a) = _
  simp only [quotEquivPowQuotPowSucc, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    LinearMap.comp_apply, Submodule.mkQ_apply]
  apply congrArg (I • ⊤ : Submodule R (I ^ n : Ideal R)).mkQ
  apply Subtype.ext
  change (LinearMap.mulRight R h.principal.choose ^ n) a = a * h.principal.choose ^ n
  rw [LinearMap.pow_mulRight, LinearMap.mulRight_apply]

/-- The inverse principal-power quotient linear equivalence recovers the
coefficient class from a multiple of the chosen generator power. -/
@[simp]
theorem quotEquivPowQuotPowSucc_symm_apply_mk (a : R) :
    (quotEquivPowQuotPowSucc h h' n).symm
        (Submodule.Quotient.mk
          (⟨a * h.principal.choose ^ n,
            Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
              (h.principal.choose_spec.ge (Ideal.mem_span_singleton_self _)) n)⟩ :
            (I ^ n : Ideal R))) =
      Quotient.mk I a := by
  rw [← quotEquivPowQuotPowSucc_apply_mk h h' n a]
  exact (quotEquivPowQuotPowSucc h h' n).symm_apply_apply (Quotient.mk I a)

/-- The plain principal-power quotient equivalence has the same formula on
representatives as the linear equivalence. -/
@[simp]
theorem quotEquivPowQuotPowSuccEquiv_apply_mk (a : R) :
    quotEquivPowQuotPowSuccEquiv h h' n (Quotient.mk I a) =
      Submodule.Quotient.mk
        (⟨a * h.principal.choose ^ n,
          Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
            (h.principal.choose_spec.ge (Ideal.mem_span_singleton_self _)) n)⟩ :
          (I ^ n : Ideal R)) :=
  quotEquivPowQuotPowSucc_apply_mk h h' n a

/-- The inverse plain principal-power quotient equivalence recovers the same
coefficient class as the inverse linear equivalence. -/
@[simp]
theorem quotEquivPowQuotPowSuccEquiv_symm_apply_mk (a : R) :
    (quotEquivPowQuotPowSuccEquiv h h' n).symm
        (Submodule.Quotient.mk
          (⟨a * h.principal.choose ^ n,
            Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
              (h.principal.choose_spec.ge (Ideal.mem_span_singleton_self _)) n)⟩ :
            (I ^ n : Ideal R))) =
      Quotient.mk I a :=
  quotEquivPowQuotPowSucc_symm_apply_mk h h' n a

end Ideal
