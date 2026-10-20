namespace P2MW.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Manifold Matrix

namespace A2EIS

open UpperHalfPlane EisensteinSeries CongruenceSubgroup Filter ModularForm

variable {N : ℕ} {k : ℤ}

theorem tendsto_eisensteinSeries [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    Tendsto (eisensteinSeries a k) atImInfty (𝓝 (cst k a)) := by
  have hstrip := tendsto_eisensteinSeries_strip hk a
  rw [tsum_lim] at hstrip

  choose n hn using fun z : ℍ => ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N)
  set red : ℍ → ℍ := fun z => ModularGroup.T ^ ((N : ℤ) * n z) • z with hred
  have hE : ∀ z, eisensteinSeries a k (red z) = eisensteinSeries a k z := fun z =>
    eisensteinSeries_T_zpow_smul a (n z) z
  have htend : Tendsto red atImInfty (stripFilter N) := by
    rw [stripFilter, tendsto_inf]
    constructor
    · rw [atImInfty, tendsto_comap_iff]
      have : UpperHalfPlane.im ∘ red = UpperHalfPlane.im := by
        funext z
        simp only [Function.comp_apply, hred, modular_T_zpow_smul, vadd_im]
      rw [this]
      exact tendsto_comap
    · rw [tendsto_principal]
      have hev : ∀ᶠ z : ℍ in atImInfty, (1 : ℝ) ≤ z.im := (atImInfty_mem _).mpr ⟨1, fun z hz => hz⟩
      filter_upwards [hev] with z hz
      exact verticalStrip_anti_right (N : ℝ) hz (hn z)
  exact (hstrip.comp htend).congr fun z => hE z

end A2EIS
end P2MW.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le
