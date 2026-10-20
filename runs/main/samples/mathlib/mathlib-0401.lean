@[expose] public section

noncomputable section

open WithZero Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

variable (K)

variable (R)

variable {R}

variable {K v}

theorem adicCompletionIntegers.mem_units_iff_valued_eq_one {a : (v.adicCompletion K)ˣ} :
    a ∈ (v.adicCompletionIntegers K).units ↔ Valued.v a.1 = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦
     ⟨h.le, by simp [mem_adicCompletionIntegers, inv_le_one_iff₀, h.symm.le]⟩⟩
  convert! isUnit_iff_valued_eq_one.1 (Submonoid.unitsEquivIsUnitSubmonoid _ ⟨_, h⟩).2

end IsDedekindDomain.HeightOneSpectrum
end
end
