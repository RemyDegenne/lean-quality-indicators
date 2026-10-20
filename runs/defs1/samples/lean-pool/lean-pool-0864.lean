@[expose] public section

noncomputable section

namespace DimdPolyLEAN

open MeasureTheory Filter

open scoped ENNReal Topology RealInnerProductSpace

/-- `symplecticFourierRep`: symplectic Fourier Rep. -/
noncomputable def symplecticFourierRep {d : Nat}
    (F : PhaseSpace d -> ℂ) : PhaseSpace d -> ℂ :=
  fun ξ =>
    ∫ η : PhaseSpace d,
      F η * Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))

end DimdPolyLEAN
end
end
