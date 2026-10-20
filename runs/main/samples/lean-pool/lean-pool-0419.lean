@[expose] public section

open Nat

namespace CutAndProject

section Minimality

lemma count_hits_lt_D_eq_one (D s : ℕ) (r0 : ℕ) (h_s_lt : s < D) (x : ZMod D) :
    countHits D r0 s x = 1 ↔ x ∈ cyclicInterval D s (r0 : ZMod D) := by
  dsimp [countHits]
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    have h_a_in : a ∈ (Finset.range s).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x) := by
      rw [ha]
      exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h_a_in
    rw [cyclic_interval_mem]
    use a
    constructor
    · exact h_a_in.1
    · exact h_a_in.2.symm
  · intro h_in
    rw [cyclic_interval_mem] at h_in
    rcases h_in with ⟨i, hi, rfl⟩
    use i
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, h_eq⟩
      have h_eq2 : ((r0 : ZMod D) + (j : ZMod D) : ZMod D)
          = ((r0 : ZMod D) + (i : ZMod D) : ZMod D) := h_eq
      have h_eq3 : (j : ZMod D) = (i : ZMod D) := add_left_cancel h_eq2
      have h_mod : j ≡ i [MOD D] := (ZMod.natCast_eq_natCast_iff j i D).mp h_eq3
      exact Nat.ModEq.eq_of_lt_of_lt h_mod (lt_trans hj h_s_lt) (lt_trans hi h_s_lt)
    · rintro rfl
      exact ⟨hi, rfl⟩

end Minimality
end CutAndProject
end
