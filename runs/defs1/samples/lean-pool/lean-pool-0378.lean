@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

section «lp_section_1»

scoped infix:45 " ⊢₂ " => Derivation2

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Derivable2 (T : Theory L) (Γ : Finset (SyntacticFormula L)) := Nonempty (T ⊢₂ Γ)

end «lp_section_1»
end FirstOrder
end LO
end
