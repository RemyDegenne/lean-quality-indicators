namespace OAI

universe u v w

namespace SourceBurnside.CellFormula

section

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula

variable {ι : Type} [DecidableEq ι]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}

variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)

include ha

omit [DecidableEq ι] in
lemma checkerHead_exact : (checkerHead a).eval v≠0 ↔ ∃ x,c.checker=.head x := by
  cases hc : c.checker <;> simp [checkerHead,represent_int ha,cellRecord,integers,hc,checkerTag]

end
end SourceBurnside.CellFormula
end OAI
