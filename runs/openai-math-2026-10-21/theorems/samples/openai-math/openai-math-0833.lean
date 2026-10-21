namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace PositiveOrderedFace

@[simp]
theorem rank_pos {k r : ℕ} (e : PositiveOrderedFace k r) :
    0 < e.rank := by
  simp [rank]

end PositiveOrderedFace
end Erdos3.FixedDensity
end
end OAI
