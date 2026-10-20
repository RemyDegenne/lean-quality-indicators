@[expose] public section

universe uT uN

variable {T : Type uT}

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar T}

section toCFG

variable [DecidableEq T]

variable {g : ChomskyNormalFormGrammar T} [DecidableEq g.NT]

lemma Generates.match_toCFG {u : List (Symbol T g.NT)} (hu : g.toCFG.Generates u) : g.Generates u :=
  Derives.match_toCFG hu

end toCFG
end ChomskyNormalFormGrammar
end
