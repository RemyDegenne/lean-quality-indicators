public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.TwoA.Census

theorem s2Arrs_get : ∀ k < 3, s2Arrs[k]! = wordArr (s2Word k) := by
  intro k hk
  rw [s2Arrs, getElem!_pos _ _ (by simp [hk])]
  simp

end CFSG.Monster.B.Fischer
end
