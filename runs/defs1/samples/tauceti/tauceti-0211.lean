public section

noncomputable section

universe u v

namespace TauCeti

attribute [local instance] Classical.decEq

/-- The distinguished vertex over index zero in the countable join of copies of a type with a
chosen unit. -/
def universalGSpaceBasepoint (G : Type u) [One G] : universalGSpace G :=
  (indexedJoin fun _ : ℕ => G).vertex ⟨0, 1⟩

end TauCeti
end
end
