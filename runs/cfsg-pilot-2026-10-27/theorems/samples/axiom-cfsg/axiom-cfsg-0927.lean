public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup

section Five

variable {V : Type} [CommGroup V]

theorem coe_pow_mulAut (P : MulAut V) (n : ℕ) : ⇑(P ^ n) = (⇑P)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

end Five
end CFSG.Quasithin.H13.KGLie
end
