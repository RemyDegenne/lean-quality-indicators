public section

variable {S : Type*} [CommRing S] (I : Ideal S)

theorem Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk {x : S} {n : ℕ} (hn : n ≠ 0) :
    IsUnit (Ideal.Quotient.mk (I ^ n) x) ↔ IsUnit (Ideal.Quotient.mk I x) := by
  rw [← IsNilpotent.isUnit_quotient_mk_iff (I := Ideal.map (Ideal.Quotient.mk (I ^ n)) I)]
  · rw [← isUnit_map_iff (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self hn))]
    rfl
  · use n
    simp [← Ideal.map_pow]

end
