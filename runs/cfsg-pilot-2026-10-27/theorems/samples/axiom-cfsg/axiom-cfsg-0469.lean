public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

theorem A4_core {r M c R : ℕ} (hr : 1 ≤ r) (hc : 1 ≤ c) (hMc : M * c = R)
    (hR : R ≤ (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2))
    (hXM : (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) ≤ 2 * M + 1) :
    False := by
  have hMle : M ≤ M * c := Nat.le_mul_of_pos_right M (by omega)
  have hT0 : 0 < (r + 1) ^ 3 * (r * (r + 2)) :=
    Nat.mul_pos (pow_pos (by omega) 3) (Nat.mul_pos (by omega) (by omega))
  have hT1 : 1 ≤ (r + 1) ^ 3 * (r * (r + 2)) := by omega
  have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hPQ : 2 * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2) + 2 ≤ r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3 := by
    nlinarith
  have hkey : (r + 1) ^ 3 * (r * (r + 2)) * (2 * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2) + 2)
      ≤ (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) :=
    Nat.mul_le_mul (le_refl _) hPQ
  nlinarith

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
end
