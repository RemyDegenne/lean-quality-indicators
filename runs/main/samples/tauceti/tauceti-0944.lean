public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

namespace OrientedPDCode

open PDCode

variable {n : ℕ} (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
  (hqe : q ≠ D.edgePair.val p)

@[simp]
theorem alexanderWeight_insertClasp_last (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) slot =
      if b then
        ![1, T (if D.orientation q then 1 else -1), 1, T (if D.orientation q then -1 else 1)] slot
      else
        ![T (if D.orientation p then -1 else 1), 1,
          T (if D.orientation p then 1 else -1), 1] slot := by
  rw [alexanderWeight_def]
  cases b <;> cases hp : D.orientation p <;> cases hq : D.orientation q <;> fin_cases slot <;>
    simp [PDCode.isOver_def, hp, hq]

end OrientedPDCode
end TauCeti
end
end
