@[expose] public section

namespace LeanPool.AharoniKorman

namespace Hollom

local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)

lemma level_eq_range (n : ℕ) : level n = Set.range (embed n) := by simp [level, Set.range, embed]

end Hollom
end LeanPool.AharoniKorman
end
