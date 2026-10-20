@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse

/-- Structured selected-transition command. -/
noncomputable def action (tm : TM n) (state : tm.Q)
    (symbols : Fin (n + 2) → Γ) : Structured.Cmd :=
  .basics (actionOps tm state symbols)

end Sparse
end TMConfig
end RAM
end Complexity
end
