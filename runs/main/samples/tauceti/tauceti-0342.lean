public section

namespace TauCeti

variable {R : Type*} [CommRing R]

variable (R)

variable {R}

theorem ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le {n : ℕ∞}
    (h : ∀ f : R, f ≠ 0 → ringKrullDim (R ⧸ Ideal.span {f}) ≤ n) :
    ringKrullDim R ≤ n + 1 := by
  refine iSup_le fun l ↦ ?_
  obtain hl | hl := eq_or_ne l.length 0
  · rw [hl, Nat.cast_zero]
    exact_mod_cast (zero_le : (0 : ℕ∞) ≤ n + 1)
  -- The second prime `l 1` contains some `f ∉ l 0`; then `f ≠ 0`, and the tail of `l` is a
  -- chain in `V(f)`.
  let t : LTSeries (PrimeSpectrum R) := l.tail hl
  have h₀₁ : l.head.asIdeal < t.head.asIdeal := by
    rw [PrimeSpectrum.asIdeal_lt_asIdeal, RelSeries.head_tail, ← RelSeries.apply_zero]
    exact l.strictMono (Fin.pos_iff_ne_zero.mpr (by simpa [Fin.ext_iff] using hl))
  obtain ⟨f, hf₁, hf₀⟩ := IsConcreteLE.exists_of_lt h₀₁
  have hf : f ≠ 0 := by
    rintro rfl
    exact hf₀ (zero_mem _)
  let q : LTSeries (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {f})) :=
    .mk t.length (fun i ↦ ⟨t i, by
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
      exact LTSeries.head_le t i hf₁⟩) fun _ _ hij ↦ Subtype.mk_lt_mk.mpr (t.strictMono hij)
  have hq : (t.length : WithBot ℕ∞) ≤ n := (Order.LTSeries.length_le_krullDim q).trans
    ((ringKrullDim_quotient _).symm.le.trans (h f hf))
  rw [show l.length = t.length + 1 by rw [RelSeries.tail_length]; omega]
  simpa using add_le_add_left hq 1

end TauCeti
end
