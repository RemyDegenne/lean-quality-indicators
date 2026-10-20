universe u

public noncomputable section

open Cardinal

namespace Surreal.OmnificInteger

/-- Recover the omnific integer represented by a bounded nonpositive Hahn integer part. -/
def ofSmallSupportIntegerPart
    (b : SmallSupportIntegerPart.{u}) : Surreal.OmnificInteger.{u} :=
  have hb := (HahnSeries.mem_cardSuppLTTruncationIntegerPart
    (Z := Surreal.realIntegerSubring)).mp b.2
  ⟨ofSmallSupportSurreal b, Surreal.mem_omnificIntegers.mpr
    (Surreal.isOmnificInteger_iff_normalForm.mpr ⟨by
      intro i hi
      have hfull : OrderDual.toDual i ∈
          (b.1.1 : HahnSeries Surrealᵒᵈ ℝ).support := by
        rw [← toFullHahnSeries_ofSmallSupportSurreal]
        exact Surreal.mem_support_toFullHahnSeries.mpr hi
      have hnonpos := hb.1 hfull
      change 0 ≤ i at hnonpos
      exact hnonpos, by
      rw [← Surreal.mem_realIntegerSubring]
      have hcoeff := congrArg
        (fun q : HahnSeries Surrealᵒᵈ ℝ ↦ q.coeff 0)
        (toFullHahnSeries_ofSmallSupportSurreal b)
      rw [Surreal.coeff_toFullHahnSeries] at hcoeff
      have hcoeff' : (ofSmallSupportSurreal b).coeff 0 =
          (b.1.1 : HahnSeries Surrealᵒᵈ ℝ).coeff 0 := by
        simpa using hcoeff
      rw [hcoeff']
      exact hb.2⟩)⟩

end Surreal.OmnificInteger
end
