@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory NumberField NumberField.Units
  NumberField.InfinitePlace

open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

variable [IsTotallyComplex K]

theorem summable_integral_norm_idealSet_complexPlaceMellinGaussian
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun a : idealSet K J ↦
        ∫ q : InfinitePlace K → ℝ,
          ‖complexPlaceMellinGaussian K (idealSetElement K J a) s q‖
          ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) := by
  have hbase :=
    (summable_idealSet_inverseNormPower K J
      (s := (s.re : ℂ)) hs).norm
  refine (hbase.mul_left
    ‖((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor (s.re : ℂ)) ^
      nrComplexPlaces K‖).congr fun a ↦ ?_
  rw [integral_norm_complexPlaceMellinGaussian K
    (idealSetElement_ne_zero K J a) (lt_trans zero_lt_one hs),
    absNorm_idealSetElement K J a, norm_mul]
  simp

end NumberField.Odlyzko
end
end
