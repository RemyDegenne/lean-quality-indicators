@[expose] public section

open HurwitzZeta Complex ZMod Finset Filter Set

open scoped Topology

open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

local notation "𝕖" => stdAddChar

section signed

variable {Φ : ZMod N → ℂ}

theorem completedLFunction_one_sub_even (hΦ : Φ.Even) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0) (hs₁ : s ≠ 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  -- We prove this using `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, so we need to
  -- gather up the ingredients for this big theorem.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * completedLFunction (𝓕 Φ) t
  -- Set on which F, G are analytic:
  let U := {t : ℂ | (t ≠ 0 ∨ ∑ j, Φ j = 0) ∧ (t ≠ 1 ∨ Φ 0 = 0)}
  -- Properties of U:
  have hsU : s ∈ U := ⟨hs₀, hs₁⟩
  have h2U : 2 ∈ U := ⟨.inl two_ne_zero, .inl (OfNat.ofNat_ne_one _)⟩
  have hUo : IsOpen U := (isOpen_compl_singleton.union isOpen_const).inter
    (isOpen_compl_singleton.union isOpen_const)
  have hUp : IsPreconnected U := by
    -- need to write `U` as the complement of an obviously countable set
    let Uc : Set ℂ := (if ∑ j, Φ j = 0 then ∅ else {0}) ∪ (if Φ 0 = 0 then ∅ else {1})
    have : Uc.Countable := by
      apply Countable.union <;>
      split_ifs <;>
      simp only [countable_singleton, countable_empty]
    convert (this.isConnected_compl_of_one_lt_rank ?_).isPreconnected using 1
    · ext x
      by_cases h : Φ 0 = 0 <;>
      by_cases h' : ∑ j, Φ j = 0 <;>
      simp [U, Uc, h, h', and_comm]
    · simp only [rank_real_complex, Nat.one_lt_ofNat]
  -- Analyticity on U:
  have hF : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    refine (differentiableAt_completedLFunction Φ _ ?_ ?_).comp t (differentiableAt_id.const_sub 1)
    exacts [ht.2.imp_left (sub_ne_zero.mpr ∘ Ne.symm), ht.1.imp_left sub_eq_self.not.mpr]
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    apply ((differentiableAt_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul
    apply differentiableAt_completedLFunction _ _ (ht.1.imp_right fun h ↦ dft_apply_zero Φ ▸ h)
    exact ht.2.imp_right (fun h ↦ by simp only [← dft_apply_zero, dft_dft, neg_zero, h, smul_zero])
  -- set where we know equality
  have hV : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := eventually_of_mem hV <| fun t ht ↦ by
    simpa only [F, G, pow_zero, mul_one] using completedLFunction_one_sub_of_one_lt_even hΦ ht
  -- now apply the big hammer to finish
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUp h2U hFG hsU

end signed
end ZMod
end
