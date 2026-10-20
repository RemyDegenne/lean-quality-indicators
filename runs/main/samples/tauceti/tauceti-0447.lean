public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

theorem exists_eq_sum_teichmullerCoeff_add_pow_mul (x : 𝕎 R) (m : ℕ) :
    ∃ b : 𝕎 R, x = ∑ i ∈ Finset.range m, teichmuller p (x.teichmullerCoeff i) * (p : 𝕎 R) ^ i +
      (p : 𝕎 R) ^ m * b := by
  cases m with
  | zero => exact ⟨x, by simp⟩
  | succ n =>
    obtain ⟨b, hb⟩ := pow_dvd_sub_sum_teichmullerCoeff x n
    exact ⟨b, by rw [Nat.range_succ_eq_Iic, ← hb, add_sub_cancel]⟩

end WittVector
end
