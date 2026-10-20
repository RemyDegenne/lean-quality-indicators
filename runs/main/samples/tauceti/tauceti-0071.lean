public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {L : Type*} [Field L] [CharZero L] {F : IntermediateField ℚ L} {ζ : L} {N : ℕ}

theorem exists_mem_sq_eq_intCast (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F) {m : ℤ}
    (hdvd : 4 * m.natAbs ∣ N) :
    ∃ x ∈ F, x ^ 2 = (m : L) := by
  obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_natCast hN hζ hmem hdvd
  rcases m.natAbs_eq with hm' | hm'
  · have hcast : ((m : L)) = ((m.natAbs : ℕ) : L) := by rw [hm']; simp
    exact ⟨x, hxF, by rw [hx, hcast]⟩
  · have h4N : 4 ∣ N := (dvd_mul_right 4 m.natAbs).trans hdvd
    obtain ⟨i, hiF, hi⟩ := exists_mem_sq_eq_neg_one (hζ.pow hN (Nat.div_mul_cancel h4N).symm)
      (pow_mem hmem _)
    have hcast : ((m : L)) = -((m.natAbs : ℕ) : L) := by
      rw [hm']
      simp
    refine ⟨i * x, mul_mem hiF hxF, ?_⟩
    rw [mul_pow, hi, hx, hcast]
    ring

end TauCeti.Multiquadratic
end
