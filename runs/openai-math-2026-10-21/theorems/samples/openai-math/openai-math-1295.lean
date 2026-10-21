namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Filter Set

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_chart_contDiffAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ContDiffAt ℝ 1 (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  let t := F.time / 2
  have ht0 : 0 < t := half_pos F.time_pos
  have ht : t ∈ Ioo (-F.time) F.time := by
    dsimp [t]
    constructor <;> linarith [F.time_pos]
  have hinit : ContDiffAt ℝ 1
      (fun v : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  have hF : ContDiffAt ℝ 1 (fun z => F.map (z, t))
      (chartAt FourSpace c e.base, frameMomentumMap g c e 0) := by
    simpa only [map_zero] using F.contDiffAt_slice _ (Metric.mem_ball_self F.radius_pos) t ht
  have hlocal : ContDiffAt ℝ 1
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v))) 0 := by
    have hcompose : ContDiffAt ℝ 1 (fun v : FourSpace =>
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)) 0 :=
      ContDiffAt.comp (f := fun v : FourSpace =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v))
        (g := fun z : CotangentCoordinates => F.map (z, t)) 0 hF hinit
    exact hcompose.fst.congr_of_eventuallyEq
      (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0)
  have hscale : ContDiffAt ℝ 1 (fun v : FourSpace => t⁻¹ • v) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff.contDiffAt
  have hlocal' : ContDiffAt ℝ 1
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t⁻¹ • (0 : FourSpace)) := by simpa only [smul_zero] using hlocal
  have h := hlocal'.comp 0 hscale
  have heq : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  change ContDiffAt ℝ 1 (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v)))) 0 at h
  rwa [heq] at h

end
end PositiveEinsteinFour.Geometry
end
end OAI
