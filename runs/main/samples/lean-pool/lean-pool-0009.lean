@[expose] public section

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter

open scoped ContDiff Topology InnerProductSpace BigOperators

open PrimaryPulseBounds

section WeightedPressure

open WeightedClasses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {s : StripData E} {w : ℕ → E → ℝ} {α : ℝ}

theorem pressure_class
    {N Ndot a f : ℕ → E → ProblemStatement.Space}
    {A : ℕ → E → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) N)
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    (ha : MemClass s w α a) (hf : MemClass s w α f)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)
    {frequency : ℕ → ℝ} (hfreq : BandBound s (1 / 2) (fun n => 1 / frequency n)) :
    MemClass s w (α + 1 / 2) (fun n x => Complex.I *
      (TangentProjection.pressureCoefficient (N n x) (Ndot n x) (a n x)
        (A n x (a n x)) (f n x) : ℂ) / (frequency n : ℂ)) := by
  have hpc := (pressureCoefficient_class hN hNdot hA ha hf hb hlower hupper).map Complex.ofRealCLM
  have hh := (LinearWaveBounds.constant_complex_mul hpc Complex.I).band_smul hfreq
  simpa only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, one_div,
    div_eq_mul_inv, mul_comm, mul_one, Complex.ofReal_inv, Complex.ofRealCLM_apply] using hh

end WeightedPressure
end NavierStokes.ParticularWaveBounds
end
end
