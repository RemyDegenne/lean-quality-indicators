public section

namespace TauCeti

open Matrix

local instance fact_prime_seven_cyclicThree : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The displayed exact table, embedded in `ℂ` and reindexed by actual conjugacy classes. -/
noncomputable def cyclicGroupThreeComplexCharacterTable :
    Matrix (Fin (Nat.card (ConjClasses (Multiplicative (ZMod 3)))))
      (ConjClasses (Multiplicative (ZMod 3))) ℂ :=
  (cyclicClassData 3).complexTableOfCyclotomic 3 cyclicGroupThreeExactCharacterTable

end TauCeti
end
