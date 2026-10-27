public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem fixed_pow {s : MulAut (Multiplicative V4)} {x : Multiplicative V4} (hx : s x = x) (k : ℕ) :
    (s ^ k) x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

end CFSG.Quasithin.H13.U43
end
