@[expose] public section

noncomputable section

namespace NavierStokes.LocalPhysicalCopyBounds

open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds

open scoped Topology ContDiff BigOperators

variable {H Δ : ℕ} {K : Type*} {f : CopyFamily H K} {a b h r0 Z : ℝ}

theorem SupportData.sum_locally_finite (hr : SupportData f a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ s : Finset (WaveIndex H), s.card ≤ 2250 * (2 * H + 1) ∧
      f.sum a h r0 =ᶠ[𝓝 w] fun y => ∑ I ∈ s, f.periodized a h r0 I y := by
  obtain ⟨s, hs, he⟩ := masked_finsum_eventually hh hh1 (f.periodized a h r0)
    hr.periodized_support hw
  exact ⟨s, waveRegion_card_le (physicalQ_pos hh hh1 hw) s (fun I hI => (hs I).mp hI), he⟩

end NavierStokes.LocalPhysicalCopyBounds
end
end
