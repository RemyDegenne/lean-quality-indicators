public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof

open Matrix

variable {L : Type*} [Field L]

section Elements

variable {G : Type*} [Group G]

theorem threeElt_conj (g : G) {a : G} (ha : ∃ k : ℕ, a ^ 3 ^ k = 1) :
    ∃ k : ℕ, (g⁻¹ * a * g) ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_⟩
  have h := conj_pow (a := g⁻¹) (b := a) (i := 3 ^ k)
  rw [inv_inv] at h
  rw [h, hk, mul_one, inv_mul_cancel]

end Elements
end CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof
end
