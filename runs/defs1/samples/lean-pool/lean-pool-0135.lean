@[expose] public section

namespace BeyondBethe

/-- Assigns `y` to left variables and `-z` to right variables in the recursive paired-variable
encoding. -/
def pairVariablesSignedRealPoint :
    ∀ n : ℕ, (Fin n → ℝ) → (Fin n → ℝ) → PairVariables n → ℝ
  | 0, _, _, i => PEmpty.elim i
  | _n + 1, y, _z, none => y 0
  | _n + 1, _y, z, some none => -z 0
  | n + 1, y, z, some (some i) =>
      pairVariablesSignedRealPoint n (fun j ↦ y j.succ) (fun j ↦ z j.succ) i

end BeyondBethe
end
