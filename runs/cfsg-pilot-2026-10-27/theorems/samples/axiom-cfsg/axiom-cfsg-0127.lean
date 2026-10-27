public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem

open CFSG.LieType.Universal.Spin

theorem levTwoS2d_toStdD_rRefl_gen (n : ℕ) (hn : 4 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (v : Fin n → ℤ) :
    toStdD n
        (weylAction (isFiniteType_cartanD n)
          (rRefl (isFiniteType_cartanD n)
            (levTwoS2d_ofCoord n a b s t hab hs ht)) v) =
      toStdD n v - (s * toStdD n v a + t * toStdD n v b) •
        (Pi.single a s + Pi.single b t) := by
  set β := levTwoS2d_ofCoord n a b s t hab hs ht with hβdef
  have hβ : IsRt (isFiniteType_cartanD n) β := levTwoS2d_ofCoord_isRt n a b s t hab hs ht
  have hβc : toStdD n β = Pi.single a s + Pi.single b t := levTwoS2d_ofCoord_toStdD n a b s t hab hs ht
  have hk : ((s * toStdD n v a + t * toStdD n v b : ℤ) : ℚ) *
      form (isFiniteType_cartanD n) (toRat β) (toRat β) =
      2 * form (isFiniteType_cartanD n) (toRat β) (toRat v) := by
    obtain ⟨κ, hκpos, hκ⟩ := levTwoS2d_form_coord n hn
    rw [hκ, hκ, hβc]
    push_cast
    rw [levTwoS2d_dot_add_self n hab s t, levTwoS2d_dot_add_coord n hab s t v]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> push_cast <;> ring
  rw [levTwoS2d_rRefl_apply n hn hβ hk, toStdD_sub, toStdD_smul, hβc]

end CFSG.StandardType.LevTwo
end
