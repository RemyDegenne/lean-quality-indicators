public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace Z]
  {μ : Measure X} {ν : Measure Y} {ωX : X × X → Z} {ωY : Y × Y → Z}

theorem edist_gromovWassersteinSize_le_gromovWassersteinEDist
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hp : 1 ≤ p)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (z₀ : Z) :
    edist (gromovWassersteinSize p μ ωX z₀) (gromovWassersteinSize p ν ωY z₀) ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  let ω₀ : Unit × Unit → Z := fun _ ↦ z₀
  have hμ : gromovWassersteinEDist p μ ωX (Measure.dirac ()) ω₀ =
      gromovWassersteinSize p μ ωX z₀ := by
    rw [gromovWassersteinEDist_dirac_right () ω₀ hωX]
    rfl
  have hμ' : gromovWassersteinEDist p ν ωY (Measure.dirac ()) ω₀ =
      gromovWassersteinSize p ν ωY z₀ := by
    rw [gromovWassersteinEDist_dirac_right () ω₀ hωY]
    rfl
  have htri₁ := gromovWassersteinEDist_triangle (p := p) (μ := μ) (ν := ν)
    (ρ := Measure.dirac ()) (ωX := ωX) (ωY := ωY) (ωW := ω₀) hp hωX hωY
    aestronglyMeasurable_const
  have htri₂ := gromovWassersteinEDist_triangle (p := p) (μ := ν)
    (ν := μ) (ρ := Measure.dirac ()) (ωX := ωY) (ωY := ωX) (ωW := ω₀) hp hωY
    hωX aestronglyMeasurable_const
  rw [hμ, hμ'] at htri₁
  rw [hμ', hμ] at htri₂
  rw [gromovWassersteinEDist_comm] at htri₂
  rw [ENNReal.edist_le_iff_le_add_right]
  exact ⟨by simpa [add_comm] using htri₁, by simpa [add_comm] using htri₂⟩

end TauCeti
end
end
