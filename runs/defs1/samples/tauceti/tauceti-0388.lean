public section

namespace TauCeti

namespace FramedOrientedPDCode

variable {n : ℕ}

/-- Reflect a framed oriented diagram, negating its Seifert-relative framing coefficients. -/
def mirror (D : FramedOrientedPDCode n) : FramedOrientedPDCode n where
  toOrientedPDCode := D.toOrientedPDCode.mirror
  framing := fun h => -D.framing h
  framing_edgePair := by simp
  framing_oppositeCrossingSlot := by simp
  crossinglessFramings := D.crossinglessFramings.map fun component =>
    (component.1, -component.2)
  map_fst_crossinglessFramings := by simp

end FramedOrientedPDCode
end TauCeti
end
