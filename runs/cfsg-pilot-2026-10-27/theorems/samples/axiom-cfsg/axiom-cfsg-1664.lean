public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.LowTwoRank

open Matrix

namespace Item211Lie3Proof

open Item211Lie2Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem commute_of_pow_three_of_signs {G : Type*} [Group G] [HasDistribNeg G] {b u : G}
    (hu : u ≠ -u) (hb3 : b ^ 3 = 1) (hb : b * u = u * b ∨ b * u = -(u * b)) : b * u = u * b := by
  rcases hb with hb | hb
  · exact hb
  · exfalso
    apply hu
    have h1 : b * u * b⁻¹ = -u := by rw [hb, neg_mul, mul_inv_cancel_right]
    have hb3' : b * b * b = 1 := by rw [← pow_three', hb3]
    have h3 : b * (b * (b * u * b⁻¹) * b⁻¹) * b⁻¹ = -u := by
      rw [h1, mul_neg, neg_mul, h1, neg_neg, h1]
    have h4 : b * (b * (b * u * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * u * (b * b * b)⁻¹ := by group
    rw [h4, hb3', one_mul, inv_one, mul_one] at h3
    exact h3

end Item211Lie3Proof
end CFSG.RankThree.PartTwo.Sec21
end
