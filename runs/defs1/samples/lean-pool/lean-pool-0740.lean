@[expose] public section

namespace ScottishBook155

universe u

/-- A bundled real Banach space, used so that the source and target types of
the final existential statement may themselves be chosen by the construction. -/
structure RealBanachSpace where
  /-- The underlying type of the bundled real Banach space. -/
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℝ carrier]
  [completeSpace : CompleteSpace carrier]

end ScottishBook155
end
