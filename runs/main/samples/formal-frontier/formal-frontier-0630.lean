@[expose] public section

open Function IsDedekindDomain

namespace AddCommGroup

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]

theorem mem_integerPrime_iff (p : ℕ) [Fact p.Prime] (x : G) :
    x ∈ Ideal.primaryComponent G (integerPrime p).asIdeal ↔
      x ∈ primaryComponent G p := by
  rw [Ideal.primaryComponent_mem, mem_primaryComponent]
  simp only [integerPrime, Ideal.span_singleton_pow, Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨exponent, h⟩
    refine ⟨exponent, ?_⟩
    have hpow := h ⟨(p : ℤ) ^ exponent, Ideal.subset_span (Set.mem_singleton _)⟩
    simpa [← natCast_zsmul] using hpow
  · rintro ⟨exponent, hpow⟩
    refine ⟨exponent, ?_⟩
    rintro ⟨scalar, hscalar⟩
    obtain ⟨coefficient, hfactor⟩ := (Ideal.mem_span_singleton).1 hscalar
    have hint : ((p : ℤ) ^ exponent) • x = 0 := by
      simpa [← natCast_zsmul] using hpow
    change scalar • x = 0
    rw [hfactor, mul_comm, mul_smul, hint, smul_zero]

end AddCommGroup
end
