public section

namespace TauCeti.Multiquadratic

variable {q : ℕ} [Fact q.Prime]

theorem eq_of_primeDiscriminantRadicand_eq {D E : ℤ}
    (hD : IsPrimeDiscriminant D) (hE : IsPrimeDiscriminant E)
    (h : primeDiscriminantRadicand D = primeDiscriminantRadicand E) :
    D = E := by
  rcases isPrimeDiscriminant_iff.mp hD with hevD | ⟨p, hp, hpodd, rfl⟩
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · rcases hevD with rfl | rfl | rfl
      · have hE' : E = -4 :=
          (primeDiscriminantRadicand_eq_neg_one_iff (Or.inl hevE)).mp (by simpa using h.symm)
        rw [hE']
      · have hE' : E = 8 :=
          (primeDiscriminantRadicand_eq_two_iff (Or.inl hevE)).mp (by simpa using h.symm)
        rw [hE']
      · have hE' : E = -8 :=
          (primeDiscriminantRadicand_eq_neg_two_iff (Or.inl hevE)).mp (by simpa using h.symm)
        rw [hE']
    · have habs := congrArg Int.natAbs h
      rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevD,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd,
        oddPrimeDiscriminant_natAbs] at habs
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevD with h1 | h2
      · rw [h1] at habs
        exact False.elim (hq.ne_one habs.symm)
      · rw [h2] at habs
        rcases hqodd with ⟨k, hk⟩
        omega
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, _, hqodd, rfl⟩
    · have habs := congrArg Int.natAbs h
      rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd,
        primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevE,
        oddPrimeDiscriminant_natAbs] at habs
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevE with h1 | h2
      · rw [h1] at habs
        exact False.elim (hp.ne_one habs)
      · rw [h2] at habs
        rcases hpodd with ⟨k, hk⟩
        omega
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd] at h
      have hpq : p = q := by
        simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs h
      rw [hpq]

end TauCeti.Multiquadratic
end
