namespace OAI

noncomputable section

namespace MatrixMultiplication.AllFieldHistorySupport

open AllFieldHistory

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

theorem selected_classWeight_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      PermutationMatching.classWeight (selectedPositions allocation 1 D) c :=
  (selected_classWeight_formula allocation hm D c).trans
    (selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ)) D c).symm

end MatrixMultiplication.AllFieldHistorySupport
end
end OAI
