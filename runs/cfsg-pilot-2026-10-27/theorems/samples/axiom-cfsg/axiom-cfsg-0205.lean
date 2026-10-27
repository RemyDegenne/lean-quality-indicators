public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.A

open Subgroup

variable {G : Type*} [Group G]

theorem four_dvd_of_card [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {N : ℕ} [NeZero N]
    (e : ↥Q ≃* QuaternionGroup N) (h16 : 16 ≤ Nat.card ↥Q) : 4 ∣ N := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
  have hc := card_quat e
  have hn4 : 4 ≤ n := by
    by_contra hcon
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h3 : N = 2 ^ (n - 2) := by omega
  rw [h3, show n - 2 = 2 + (n - 4) by omega, pow_add]
  exact Dvd.intro _ rfl

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.A
end
