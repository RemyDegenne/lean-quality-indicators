@[expose] public section

namespace TriangleInflation

open Finset

noncomputable
section

theorem Peps_tminAI_bounds {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 64) :
    ⌊1 + ε ^ (-(1 : ℝ) / 3) / 2⌋₊ + 1 ≤ tminAI (Peps ε)
      ∧ tminAI (Peps ε) ≤ ⌊tauMinus ε⌋₊ + 1 := by
  have h8 : ε < 1 / 8 := by linarith
  have hfl : (0 : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2 := by
    have := Real.rpow_pos_of_pos h0 (-(1 : ℝ) / 3); linarith
  have hmem : (⌊tauMinus ε⌋₊ + 1) ∈ {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Peps ε)} :=
    ⟨by omega, fun h => Peps_not_nwFeasible h0 h1 (nwFeasible_of_aiFeasible h)⟩
  refine ⟨?_, Nat.sInf_le hmem⟩
  have hne : {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Peps ε)}.Nonempty := ⟨_, hmem⟩
  have hmem2 : tminAI (Peps ε) ∈ {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Peps ε)} := Nat.sInf_mem hne
  obtain ⟨hge1, hnot⟩ := hmem2
  by_contra hcon
  rw [not_le] at hcon
  have hle : ((tminAI (Peps ε) : ℕ) : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2 :=
    (Nat.le_floor_iff hfl).mp (Nat.lt_succ_iff.mp hcon)
  exact hnot (Peps_aiFeasible h0 h8 _ hge1 hle)

end
end TriangleInflation
end
