@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm

open scoped Real Manifold MatrixGroups

variable {m : ℕ}

lemma f_S_smul [Fact m.Prime] (i : Option (ZMod m)) (τ : ℍ) :
    f m i (ModularGroup.S • τ) = f m (σS m i) τ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  cases i with
  | none =>
    have htarget : σS m none = some 0 := rfl
    rw [f_none, j_smul_S_mul, htarget, f_some]
    -- matrix identity  AInf · S = S · Acol 0
    refine j_matrix_transfer ModularGroup.S _ (Acol m ((0 : ZMod m).val)) τ ?_
    apply Matrix.GeneralLinearGroup.ext
    simp [Fin.forall_fin_two, val_AInf, val_Acol, Matrix.mul_apply, Fin.sum_univ_two,
      ModularGroup.coe_S]
  | some b =>
    by_cases hb : b = 0
    · subst hb
      have htarget : σS m (some (0 : ZMod m)) = none := by simp [σS, sSfun]
      rw [f_some, j_smul_S_mul, htarget, f_none]
      -- matrix identity  Acol 0 · S = S · AInf
      refine j_matrix_transfer ModularGroup.S _ (AInf m) τ ?_
      apply Matrix.GeneralLinearGroup.ext
      simp [Fin.forall_fin_two, val_AInf, val_Acol, Matrix.mul_apply, Fin.sum_univ_two,
        ModularGroup.coe_S]
    · have htarget : σS m (some b) = some (-b⁻¹) := by simp [σS, sSfun, hb]
      rw [f_some, j_smul_S_mul, htarget, f_some]
      -- integers  B = b.val,  B' = (-b⁻¹).val,  and the quotient q with  B·B' + 1 = m·q
      set B : ℤ := (b.val : ℤ) with hB
      set B' : ℤ := ((-b⁻¹).val : ℤ) with hB'
      obtain ⟨q, hq⟩ : (m : ℤ) ∣ B * B' + 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hB, hB']
        push_cast [ZMod.natCast_zmod_val]
        rw [mul_neg, mul_inv_cancel₀ hb]; ring
      -- the SL(2,ℤ) transfer matrix  γ' = [[B, -q],[m, -B']],  det = 1
      have hdet : Matrix.det !![B, -q; (m : ℤ), -B'] = 1 := by
        rw [Matrix.det_fin_two_of]; linear_combination -hq
      set γ' : SL(2, ℤ) := ⟨!![B, -q; (m : ℤ), -B'], hdet⟩ with hγ'
      have hγ'coe : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![B, -q; (m : ℤ), -B'] := by rw [hγ']
      refine j_matrix_transfer γ' _ (Acol m B') τ ?_
      have hqR : (B : ℝ) * (B' : ℝ) - (q : ℝ) * (m : ℝ) = -1 := by
        have h : (B : ℝ) * B' + 1 = m * q := by exact_mod_cast hq
        linear_combination h
      -- matrix identity  Acol B · S = γ' · Acol B'
      apply Matrix.GeneralLinearGroup.ext
      simp [Fin.forall_fin_two, val_Acol, Matrix.mul_apply, Fin.sum_univ_two,
        ModularGroup.coe_S, hγ'coe, mul_comm]
      simpa only [sub_eq_add_neg] using hqR.symm

end Chudnovsky
end
end
