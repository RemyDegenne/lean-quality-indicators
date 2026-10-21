namespace OAI

section

noncomputable section

open Matrix Filter Set Topology

open scoped ComplexOrder Classical ContDiff

namespace Anticanonical.SourceSmooth

variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

namespace KaehlerMetric

lemma logRatio_deform_nonneg_at_globalMin (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) {x : X} (hx : ∀ y, φ.value x ≤ φ.value y) :
    0 ≤ (g.logRatio (g.deform φ hp)).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have hd := MongeAmpere.det_re_add_posSemidef _ _ (g.positive i _ hz)
    (φ.hessian_posSemidef_at_globalMin hx i hi)
  change 0 ≤ g.logRatioValue (g.deform φ hp) x
  rw [g.logRatioValue_local _ i hi]
  apply sub_nonneg.mpr
  exact Real.log_le_log (g.volumeCoefficient_pos i hz) hd

end KaehlerMetric
end Anticanonical.SourceSmooth
end
end
end OAI
