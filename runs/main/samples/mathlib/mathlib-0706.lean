@[expose] public section

macro (name := aesop_graph) "aesop_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

macro (name := aesop_graph?) "aesop_graph?" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop? $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

macro (name := aesop_graph_nonterminal) "aesop_graph_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, warnOnNonterminal := false })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

open Finset Function

universe u v w

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G H : SimpleGraph V) {a b c u v w : V} {e : Sym2 V}

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

variable (G₁ G₂)

theorem edgeSet_iSup {ι : Sort*} {f : ι → SimpleGraph V} :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by
  ext ⟨x, y⟩
  simp

end EdgeSet
end SimpleGraph
end
