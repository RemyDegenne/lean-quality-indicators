set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

@[expose] public section

universe u

namespace Ideal

theorem colon_quotient_mk_mul_eq_span_singleton
    {R : Type u} [CommRing R] [IsCancelMulZero R]
    (factor witness : R) (hWitness : witness ≠ 0) :
    (⊥ : Submodule R (R ⧸ span {factor * witness})).colon
      {Ideal.Quotient.mk (span {factor * witness}) witness} = span {factor} := by
  ext scalar
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, mul_comm factor witness, mul_comm scalar witness,
    mul_dvd_mul_iff_left hWitness, Ideal.mem_span_singleton]

end Ideal
end
