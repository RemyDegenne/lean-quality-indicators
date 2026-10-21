namespace OAI

namespace EditApproximation

@[simp] theorem queryHistoryEqualWithWork_value {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) :
    (queryHistoryEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryHistoryEqualWithWork, Bool.and_eq_true, coordinateEqualWithWork_value,
    naturalEqualWithWork_value, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hi, hq⟩, ht⟩
    exact Prod.ext hi (Prod.ext ht hq)
  · intro h
    subst b
    exact ⟨⟨rfl, rfl⟩, rfl⟩

end EditApproximation
end OAI
