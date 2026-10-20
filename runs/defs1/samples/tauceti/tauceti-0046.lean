public section

namespace TauCeti

section

variable {K : Type*} [NormedCommRing K] [NormOneClass K] [CompleteSpace K]
  [IsUltrametricDist K]

/-- The analytic sixth Tate coefficient, obtained from integral coefficients before reducing to
the residue characteristic of the ring. -/
noncomputable def tateCurveA₆ (q : K) (hq : ‖q‖ < 1) : K :=
  evalIntSeries q hq tateCurve.a₆

end
end TauCeti
end
