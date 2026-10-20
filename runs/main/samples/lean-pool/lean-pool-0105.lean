@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Function Filter MeasureTheory

open scoped BigOperators ContDiff Topology

namespace NavierStokes.TerminalCompensation

theorem physicalProfile_family_contDiffOn (P : Patch) (lam R : ℝ) (hR : 0 < R)
    {U : Set ℝ} {a : ℝ → ℝ} {c : ℝ → Coeff}
    (ha : ContDiffOn ℝ ∞ a U) (hc : ContDiffOn ℝ ∞ c U) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => physicalProfile P lam R (a z.1) (c z.1) z.2) (U ×ˢ Ioi 0) := by
  have ha' : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => a z.1) (U ×ˢ Ioi 0) :=
    ha.comp contDiffOn_fst (fun z hz => hz.1)
  have hb : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => baseProfile lam (z.2 / R)) (U ×ˢ Ioi 0) := by
    intro z hz
    exact ((Real.contDiffAt_rpow_const_of_ne (div_pos hz.2 hR).ne').comp z
      (contDiffAt_snd.div_const R)).contDiffWithinAt
  have hr : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => correction P (c z.1) (z.2 / R)) (U ×ˢ Ioi 0) :=
    (correction_family_contDiffOn P hc).comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.div_const R)) (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact ha'.mul (hb.add hr)

end NavierStokes.TerminalCompensation
end
end
