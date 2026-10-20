public section

namespace YoungDiagram

variable {μ : YoungDiagram} {c d : ℕ × ℕ} {i j : ℕ}

namespace IsCorner

theorem below_notMem (h : IsCorner μ c) : (c.1 + 1, c.2) ∉ μ := h.2.2

end IsCorner
end YoungDiagram
end
