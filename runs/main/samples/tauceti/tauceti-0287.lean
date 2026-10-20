public section

namespace TauCeti

namespace PDE

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace

open scoped Convolution

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {z : EuclideanSpace ℝ (Fin (n + 1))}
  {R : ℝ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
  {u : W1p0 volume Omega 2}

theorem IsWeakSolutionDirichlet.exists_harmonicOnNhd_value_ae_eq (hn : 2 ≤ n)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z R)
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] f)
    (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g u) :
    ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, HarmonicOnNhd h (ball z R) ∧
      ContinuousOn h (closedBall z R) ∧ EqOn h (newtonianKernel (n + 1) ⋆ f) (sphere z R) ∧
      W1p.value (u : W1p volume Omega 2)
        =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
          newtonianKernel (n + 1) ⋆ f - h := by
  obtain ⟨h, hh, hhc, hhG⟩ := exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
    (contDiff_newtonianKernel_convolution (n := n + 1) hf hc).continuous.continuousOn
  exact ⟨h, hh, hhc, hhG,
    hu.value_ae_eq_newtonianKernel_convolution_sub hn hf hc hh hhc hhG hΩ hg⟩

end PDE
end TauCeti
end
