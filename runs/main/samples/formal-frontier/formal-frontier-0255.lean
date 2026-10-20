@[expose] public section

universe u v

theorem Ideal.height_under_le_of_hasGoingDown
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (I : Ideal S) :
    (I.under R).height ≤ I.height := by
  rw [I.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun P hP ↦ ?_
  have := hP.isPrime
  exact (Ideal.height_mono (Ideal.comap_mono hP.le)).trans
    (height_under_le_of_isPrime P)

end
