@[expose] public section

open scoped BigOperators

namespace BeyondBethe

@[simp] theorem betheFloorCutNormal_last {m : ℕ}
    (i j : Fin (m + 1)) :
    betheFloorCutNormal i j (Fin.last (m * m)) = 0 := by
  simp [betheFloorCutNormal]

end BeyondBethe
end
