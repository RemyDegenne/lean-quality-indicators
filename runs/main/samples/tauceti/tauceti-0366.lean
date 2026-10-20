public section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped NumberField NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem IsAlgebraic.baseChange {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    (baseChange L χ).IsAlgebraic := by
  rw [isAlgebraic_iff, infinityType_baseChange,
    ← ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff]
  exact ((ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff _).2
    (isAlgebraic_iff.1 hχ)).baseChange

end HeckeCharacter
end TauCeti.GlobalNumberFields
end
end
