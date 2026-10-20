public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N p L : ℕ} {k : ℤ}

theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N) {L : ℕ} (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ F : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k, F ∈ cuspFormCharSpace k χ₀ ∧
      ∀ m, Nat.Coprime m L → (qExpansion 1 F).coeff m = (qExpansion 1 f).coeff (p * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg, hgcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul χ hf hp hpN hcomp hL hLN
      hpL hvan
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcount : (descendMatrixCount p N : ℂ) ≠ 0 := by
    by_cases h : p ^ 2 ∣ N
    · rw [descendMatrixCount_of_sq_dvd h]
      exact hp0
    · rw [descendMatrixCount_of_not_sq_dvd h]
      exact_mod_cast p.succ_ne_zero
  refine ⟨((p : ℂ) / descendMatrixCount p N) • descendCuspForm k hp hpN hcomp hf,
    Submodule.smul_mem _ _ (descendCuspForm_mem_cuspFormCharSpace k hp hpN hcomp hf),
    fun m hm ↦ ?_⟩
  rw [FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul, coe_descendCuspForm,
    qExpansion_coeff_descendSlash_eq_of_coprime hp hpN hL hpL hcomp hf hvan hg hgcoeff m hm,
    hgcoeff m, ite_eq_left hm]
  field_simp

end TauCeti
end
