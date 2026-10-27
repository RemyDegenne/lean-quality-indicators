@[expose] public section

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower

open Stage5AboveTwoLowerS5A2Envelope

/-- The next algorithm query, with the first query fixed at the origin. -/
noncomputable def stepQuery (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : Point d :=
  if t = 0 then 0 else P.algorithm.nextQuery 0 state.obsPrefix

end V7.Stage5AboveTwoLowerS5F
end
