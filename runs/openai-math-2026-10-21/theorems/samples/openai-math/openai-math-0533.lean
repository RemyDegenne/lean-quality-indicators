namespace OAI

namespace EditApproximation

theorem arithmeticFlatMapWithWork_value {α β : Type*} (f : α → List β × ℕ) (values : List α) :
    (arithmeticFlatMapWithWork f values).1 = values.flatMap (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [arithmeticFlatMapWithWork, ih, List.flatMap_cons]

end EditApproximation
end OAI
