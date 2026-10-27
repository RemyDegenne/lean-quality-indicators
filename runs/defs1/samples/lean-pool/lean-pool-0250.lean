@[expose] public section

noncomputable section

namespace NavierStokes.ScaledTangentTransport

open Set Function CommonCoverSolve TorusInverse ParticularWaveBounds HarmonicCalculus

open scoped Topology ContDiff InnerProductSpace

section Inputs

variable {P Q H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The velocity scale is `amplitude`.  The actual source scale is
`rate * amplitude`, and the moving normal acquires both normal and clock
scales in its slot derivative. -/
noncomputable def transportTangent (t : TangentData P H) (parameter : Q → P)
    (gap : ℕ) (shift rate amplitude normalScale : ℝ) : TangentData Q H where
  normal z := normalScale • t.normal (parameter z.1, CopySolveCompatibility.nativeTimeMap shift
      rate z.2)
  normalDot z := (normalScale * rate) •
    t.normalDot (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  action z := rate • t.action (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  damping z := rate * t.damping (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  source z := (rate * amplitude) • t.source (parameter z.1, coverPower gap z.2)

end Inputs
end NavierStokes.ScaledTangentTransport
end
end
