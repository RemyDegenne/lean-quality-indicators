@[expose] public section

universe u v

namespace IsLocalization.AtPrime

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem mem_minimalPrimes_of_radical_map_eq
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime A q] (I : Ideal R)
    (h : (I.map (algebraMap R A)).radical = q.map (algebraMap R A)) :
    q ∈ I.minimalPrimes := by
  haveI : (q.map (algebraMap R A)).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (S := A) q le_rfl
  have hmin : q.map (algebraMap R A) ∈ (I.map (algebraMap R A)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, h, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  simpa only [IsLocalization.minimalPrimes_map q.primeCompl A I, Set.mem_preimage,
    Ideal.under_map_of_isLocalizationAtPrime (S := A) q le_rfl] using hmin

end IsLocalization.AtPrime
end
