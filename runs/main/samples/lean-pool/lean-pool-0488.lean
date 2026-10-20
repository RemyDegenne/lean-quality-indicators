@[expose] public section

namespace BeyondBethe

@[simp] theorem kuhnEvalStep_return_build {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (fallback : ColumnMate n) (result : KuhnSearchResult n) :
    kuhnEvalStep A
        (.ret result [.build ⟨rows, fallback⟩]) =
      kuhnBuildEvalState A rows (result.mate?.getD fallback) := by
  cases rows <;> rfl

end BeyondBethe
end
