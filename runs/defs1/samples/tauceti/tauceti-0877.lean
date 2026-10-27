public section

namespace TauCeti

namespace StandardYoungTableau

variable {μ : YoungDiagram} {c : ℕ × ℕ}

/-- The cell of a standard Young tableau of a nonempty shape that carries the largest label,
`μ.card - 1`. -/
def maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) : ℕ × ℕ :=
  (T.toTableau.symm ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ : ↥μ.cells)

end StandardYoungTableau
end TauCeti
end
