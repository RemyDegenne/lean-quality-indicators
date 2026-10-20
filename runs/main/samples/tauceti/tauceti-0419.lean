public section

namespace TauCeti

namespace OrientedPDCode

variable {n : ℕ}

@[simp]
theorem mirror_mirror (D : OrientedPDCode n) : D.mirror.mirror = D := by
  ext <;> simp

end OrientedPDCode
end TauCeti
end
