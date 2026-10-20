public section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti

open scoped MatrixGroups Pointwise ENNReal

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ))

theorem volume_compl_freeLocus [Countable Γ] :
    volume ((freeLocus Γ ℍ : Set ℍ)ᶜ) = 0 :=
  (countable_compl_freeLocus Γ).measure_zero volume

end Subgroup
end
