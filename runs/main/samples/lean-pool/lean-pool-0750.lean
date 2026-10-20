@[expose] public section

noncomputable section

namespace NavierStokes.HarmonicSourceSupport

open Set Function Filter HarmonicFields HarmonicResidual HarmonicCalculus

open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section ColoredSlots

open CorrectionState LabelSumBounds

variable {ι : Type*} {d h : ℝ} {vr vt : TorusInverse.Plane}
  {sys : PartitionedCovariance.SlotSystem d h vr vt}
  {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
  {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}

omit [NormedSpace ℝ D] in
theorem supported_product_germ (hU : IsOpen U)
    (hu : SupportedOscillations sys label χ Y U u)
    (hv : SupportedOscillations sys label χ Y U v)
    {l k : ι} {n : ℕ} (hl : 1 ≤ (label n l).1) (hk : 1 ≤ (label n k).1)
    (hne : label n l ≠ label n k) {x : D × ℝ} (hx : x.1 ∈ U) :
    ∀ᶠ y in 𝓝 x, ∀ i j,
      LinearWaveResidual.realLift (u l n) y i * LinearWaveResidual.realLift (v k n) y j = 0 := by
  filter_upwards [(liftDomain_open hU).mem_nhds ⟨hx, mem_univ x.2⟩] with y hy
  intro i j
  change (u l n y i : ℂ) * (v k n y j : ℂ) = 0
  rw [← Complex.ofReal_mul,
    supported_cross_product_zero hu hv hl hk hne hy.1 y.2 i j, Complex.ofReal_zero]

end ColoredSlots
end NavierStokes.HarmonicSourceSupport
end
end
