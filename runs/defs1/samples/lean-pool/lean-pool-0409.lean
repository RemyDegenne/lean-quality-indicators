@[expose] public section

universe u v

/-- L* algorithm (Angluin 1987): learns DFAs using membership and
    equivalence queries in polynomial time.
    The canonical exact learning algorithm. -/
structure LStar (Sym : Type*) [DecidableEq Sym] [Fintype Sym] where
  /-- The MAT providing queries -/
  teacher : MinimallyAdequateTeacher (Word Sym) Bool
  -- The observation table (implementation detail; the structure tracks the algorithm's state)
  /-- Number of states in the learned DFA -/
  numStates : ℕ
  /-- The learned DFA (after termination) -/
  result : Option (DFA' Sym (Fin (numStates + 1)))

end
