namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace P2mNormalize

section Rational

theorem exists_rat_valued_eq (n : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hn0 : ∀ w, n w ≠ 0) (hn : ∀ᶠ w in Filter.cofinite, Valued.v (n w) = 1) :
    ∃ t : ℚ, 0 < t ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) t) = Valued.v (n w) := by
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 ℚ) | ¬ Valued.v (n w) = 1}.Finite := Filter.eventually_cofinite.1 hn
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset with hS
  have hmemS : ∀ w, w ∈ S ↔ Valued.v (n w) ≠ 1 := fun w => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  let k : HeightOneSpectrum (𝓞 ℚ) → ℤ := fun w => WithZero.log (Valued.v (n w))
  have hk : ∀ w, WithZero.exp (k w) = Valued.v (n w) := fun w =>
    WithZero.exp_log ((Valuation.ne_zero_iff _).2 (hn0 w))
  let p : HeightOneSpectrum (𝓞 ℚ) → ℚ := fun w => ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ)
  have hp_pos : ∀ w, 0 < p w := fun w => by
    show (0 : ℚ) < ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ)
    exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).pos
  refine ⟨∏ w ∈ S, p w ^ (-(k w)), Finset.prod_pos fun w _ => zpow_pos (hp_pos w) _, fun w => ?_⟩
  rw [valued_algebraMap, map_prod]
  simp only [map_zpow₀]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single w]
    · rw [show p w = ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) from rfl, valuation_natGenerator_self,
        ← WithZero.exp_zsmul, smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, hk]
    · intro w' _ hw'
      rw [show p w' = ((Rat.HeightOneSpectrum.natGenerator w' : ℕ) : ℚ) from rfl,
        valuation_natGenerator_of_ne w w' hw', one_zpow]
    · intro h; exact absurd hw h
  · rw [Finset.prod_eq_one]
    · have := (hmemS w).not.1 hw
      push Not at this
      exact this.symm
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [show p w' = ((Rat.HeightOneSpectrum.natGenerator w' : ℕ) : ℚ) from rfl,
        valuation_natGenerator_of_ne w w' hne, one_zpow]

end Rational
end P2mNormalize
end
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem
