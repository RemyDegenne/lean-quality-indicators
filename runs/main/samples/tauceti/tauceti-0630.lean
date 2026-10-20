public section

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section JHolomorphic

@[simp]
lemma isConstStructureJHolomorphicWithinAt_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (c : W) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J J' (fun _ : V => c) s x :=
  (isConstStructureJHolomorphicAt_const J J' c x).isConstStructureJHolomorphicWithinAt

end JHolomorphic
end TauCeti
end
