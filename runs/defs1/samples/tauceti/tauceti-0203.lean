public section

namespace TauCeti

namespace UnimodularLieIndex

variable (d : UnimodularLieIndex)

/-- The index `F₄(q)`. -/
abbrev f4 (q : PrimePower) : UnimodularLieIndex :=
  ⟨⟨.F4 q, by simp⟩, by simp⟩

end UnimodularLieIndex
end TauCeti
end
