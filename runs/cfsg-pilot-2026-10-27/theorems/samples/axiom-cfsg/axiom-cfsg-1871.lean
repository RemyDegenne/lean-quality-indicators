public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem t310_uv_fixes_a (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t310 m hm).action.φuv
        ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k)) =
      (2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k) := by
  show (Type310.action m hm).φuv ((2 ^ (m - 1) : ℕ) • Torus.a (k := Type310.k m)) =
    (2 ^ (m - 1) : ℕ) • Torus.a (k := Type310.k m)
  dsimp only [Type310.action, SigmaFourAction.ofMatEq, SigmaFourAction.φuv, Torus.a]
  rw [map_nsmul, matAct_gen_eq]
  simp [Type310.uvM, Type310.uvA, Type310.ρM, Type310.tM, uMat, ofCols, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply, zsmul_eq_mul]
  · have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
      rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) from by norm_num]
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have h1 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 4 = 0 := by
      rw [show (4 : ZMod (2 ^ m)) = 2 ^ 2 by norm_num, ← pow_add,
        show m - 1 + 2 = m + 1 by omega, pow_succ, hzero, zero_mul]
    change (2 : ZMod (2 ^ m)) ^ (m - 1) * 4 = 0
    exact h1
  · have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
      rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) from by norm_num]
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := by
      rw [← pow_succ, show m - 1 + 1 = m by omega, hzero]
    change (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0
    exact h2

end StrothFrame.IsD
end CFSG.CGT.Stroth77
end
