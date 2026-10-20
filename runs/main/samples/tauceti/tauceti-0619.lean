public section

namespace TauCeti.OrientedPDCode

open PDCode

variable {n : ℕ}

variable (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool)
  (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)

@[simp] theorem crossingSign_insertCrossing_last :
    (D.insertCrossing p q b hqp hqe).crossingSign (Fin.last n) =
      if (D.orientation p ^^ D.orientation q) = b then 1 else -1 := by
  simp [crossingSign_def, crossing_apply]

end TauCeti.OrientedPDCode
end
