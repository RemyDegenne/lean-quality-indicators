public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

open scoped NNReal

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  {r : ℝ}

/-- **The Gauss point `η_r` of the closed unit disc**, for `0 < r ≤ 1`: the point of
`Spa (K⟨T⟩, K⟨T⟩°)` given by the Gauss valuation `f ↦ sup_n ‖aₙ‖ rⁿ`. At `r = 1` it is the Gauss
point of the disc. -/
noncomputable def gaussPoint (hr₀ : 0 < r) (hr₁ : r ≤ 1) : closedPolydisc 1 K :=
  ⟨ofValuation (closedDiscGaussValuation hr₀ hr₁), (mem_closedPolydisc_iff _ _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_closedDiscGaussValuation hr₀ hr₁),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact closedDiscGaussValuation_le_one_of_isPowerBounded hr₀ hr₁
          (mem_powerBoundedSubring.mp hf)⟩⟩

end NontriviallyNormedField
end TauCeti.ValuationSpectrum
end
