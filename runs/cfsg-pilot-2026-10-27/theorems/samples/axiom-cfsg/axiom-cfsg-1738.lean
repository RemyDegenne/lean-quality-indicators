public section

namespace CFSG.GH74.Generic

open Module Matrix CFSG.Assembly.LowTwoRank

section SpLA

variable {F : Type} [Field F]

theorem eq_zero_of_sp2Form_right {u : Fin 2 ⊕ Fin 2 → F} (h : ∀ v, sp2Form u v = 0) : u = 0 := by
  by_contra hu
  have hJ : u ᵥ* sp2Gram F ≠ 0 := by
    intro h0
    apply hu
    have : u ᵥ* sp2Gram F ᵥ* sp2Gram F = 0 := by rw [h0, zero_vecMul]
    rw [vecMul_vecMul, sp2Gram_mul_self, vecMul_neg, vecMul_one, neg_eq_zero] at this
    exact this
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hJ
  have := h (Pi.single b 1)
  rw [sp2Form, dotProduct_mulVec, dotProduct_single, mul_one] at this
  exact hb (by simpa using this)

end SpLA
end CFSG.GH74.Generic
end
