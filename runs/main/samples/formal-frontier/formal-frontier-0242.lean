@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [IsDomain R] {I : Ideal R}
  (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ)

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
end
