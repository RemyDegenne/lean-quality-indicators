@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The index permutation that interchanges the two blue children. -/
def swapBlueIndexEquiv : SixPointIndex ≃ SixPointIndex where
  toFun
    | (.red, label) => (.red, label)
    | (.blue, label) => (.blue, swapChildLabel label)
  invFun
    | (.red, label) => (.red, label)
    | (.blue, label) => (.blue, swapChildLabel label)
  left_inv index := by
    rcases index with ⟨color, label⟩
    cases color <;> cases label <;> rfl
  right_inv index := by
    rcases index with ⟨color, label⟩
    cases color <;> cases label <;> rfl

end LeanPool.Besicovitch
end
end
