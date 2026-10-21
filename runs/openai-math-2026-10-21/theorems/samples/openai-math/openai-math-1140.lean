namespace OAI

open Set Filter

namespace DefocusingNLS

theorem exists_radialExterior_boundary_free_limit
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ))
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (ν m : ℕ → ℂ)
    (hν : Tendsto ν atTop
      (nhds (2*Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ))))
    (hm : Tendsto m atTop
      (nhds (radialFreeBoundaryCoefficient ((ProfileCertificate.centerB : ℝ)+w.val.re) h))) :
    let q := -Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)
    let m₀ := radialFreeBoundaryCoefficient ((ProfileCertificate.centerB : ℝ)+w.val.re) h
    ∃ Z : ℕ → ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z (radialFreeSlowJet q m₀) atTop
        (Ici (Real.log innerBoundaryRadius)) ∧
      (∀ n, Tendsto (Z n) atTop (nhds (m n,0))) ∧
      ∀ᶠ n in atTop, ∀ t, Real.log innerBoundaryRadius ≤ t →
        (Z n t).1 ≠ 0 ∧ HasDerivAt (Z n)
          ((Z n t).2,-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  intro q m₀
  obtain ⟨hn,hvalue⟩ := radialFreeBoundaryCoefficient_spec w h hh
  have hsmall : ‖radialFreeSlowValue q m₀ (Real.log innerBoundaryRadius)‖ < 1 := by
    rw [hvalue,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
    exact hh1
  obtain ⟨δ,ρ,hd,hdm,hm1,hρ,hupper,hlower⟩ := radialFreeSlow_annulus w m₀ hn hsmall
  apply exists_radialExterior_extended_tail ν m q m₀ (by simp [q]) _ hm δ ρ
    (Real.log innerBoundaryRadius) hd hdm hm1 hρ hupper hlower
  convert hν using 1
  dsimp [q]
  congr 1
  ring

end DefocusingNLS
end OAI
