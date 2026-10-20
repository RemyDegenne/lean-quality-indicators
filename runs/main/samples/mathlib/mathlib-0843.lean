public section

variable {S : Type*} [CommRing S] (I : Ideal S)

theorem Ideal.Quotient.isUnit_mk_pow_of_notMem [I.IsMaximal] {n : ℕ} {x : S} (hx : x ∉ I) :
    IsUnit (mk (I ^ n) x) := by
  by_cases! hn : n = 0
  · rw [pow_eq_top_iff.mpr (Or.inr hn)]
    exact isUnit_of_subsingleton _
  exact (isUnit_mk_pow_iff_notMem I hn).mpr hx

end
