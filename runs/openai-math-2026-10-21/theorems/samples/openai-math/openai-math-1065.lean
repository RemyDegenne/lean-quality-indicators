namespace OAI

namespace FiniteCircle

open scoped BigOperators List

open scoped ComplexConjugate

open RCLike Module

open Classical

theorem histogram_eq_zero {X Y : Type*} (label : X → Y) (xs : List X) (y : Y)
    (h : ∀ x ∈ xs, label x ≠ y) : histogram label xs y = 0 := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [histogram_cons, ite_eq_right (h x (by simp)), zero_add]
    exact ih (fun z hz => h z (by simp [hz]))

end FiniteCircle
end OAI
