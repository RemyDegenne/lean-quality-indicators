public section

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section JHolomorphic

lemma IsConstStructureJHolomorphicWithinAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W} {x : V}
    (hg : IsConstStructureJHolomorphicWithinAt J' J'' g t (f x))
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hst : Set.MapsTo f s t) :
    IsConstStructureJHolomorphicWithinAt J J'' (g ∘ f) s x := by
  refine ⟨_, hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt hst, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

end JHolomorphic
end TauCeti
end
