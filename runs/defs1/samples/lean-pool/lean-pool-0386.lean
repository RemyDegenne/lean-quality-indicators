@[expose] public section

noncomputable section

namespace NavierStokes.SlowRecursion

open Set Filter

open scoped Topology ContDiff

/-- Step component as an element of `AxisFunction S U`. -/
noncomputable def stepComponent {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) : AxisFunction S U := by
  let W := stepRaw c hS C n F
  have hdata := sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2 i) (Ioo (-S) S ×ˢ U) := by
    simpa only [W, stepRaw, VolterraRegularity.radialDomain, Real.ball_eq_Ioo,
      zero_sub, zero_add] using
      (contDiffOn_pi.mp (PositiveAxisExistence.positiveSolution_jointly_smooth hS.le hSR c.open_set
        ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata) i)
  have hw := PositiveAxisExistence.positiveSolution_spec hS.le hSR c.open_set
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata
  have hh : ∀ r ∈ Ioo (-S) S, DifferentiableOn ℂ (fun z => W r z i) U :=
    fun r hr => hw.parameter_holomorphic r ⟨hr.1.le, hr.2.le⟩ i
  have he : ∀ z ∈ U, ∀ r ∈ Ioo (-S) S, W (-r) z i = W r z i := by
    intro z hz r hr
    apply VolterraParity.first_components_even (i := i)
      (fun r hr z hz => PositiveAxisExistence.positiveSolution_parity hS.le hSR c.open_set
        ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata hr hz) hi hz r hr
  exact symmetrize c.open_set c.conjugate (fun p => W p.1 p.2 i) hs hh he

end NavierStokes.SlowRecursion
end
end
