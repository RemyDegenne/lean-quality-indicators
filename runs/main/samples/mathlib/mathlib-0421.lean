@[expose] public section

open Filter Set WithTop.LinearOrderedAddCommGroup

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {R : Type*} [NormedRing R] [NoZeroDivisors R]
  [Module R E] [IsBoundedSMul R E] [Module.IsTorsionFree R E]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f f₁ f₂ : 𝕜 → E} {x : 𝕜}

theorem meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) ≤ meromorphicOrderAt (f₁ + f₂) x := by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₂f₁, min_top_left, meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to ℤ using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x to ℤ using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z ↦ (z - x) ^ (n₁ - n)) • g₁ + (fun z ↦ (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[≠] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr this, meromorphicOrderAt_smul t₀ h₁g.meromorphicAt, t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg

end
