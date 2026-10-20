@[expose] public section

universe uN uT

namespace ContextFreeGrammar

variable {T : Type uT}

section EliminateUnitRules

variable {g : ContextFreeGrammar T} [DecidableEq g.NT]

/-- Computes non-unit rules for all unit pairs -/
noncomputable def removeUnitRules [DecidableEq T] (l : Finset (g.NT × g.NT)) :=
  ((l.toList).map computeUnitPairRules).flatten.toFinset

end EliminateUnitRules
end ContextFreeGrammar
end
