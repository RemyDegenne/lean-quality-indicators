namespace OAI

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT.TreeCoding

namespace PlaneTree

lemma build_append (l l' : List ℕ) (ts : List PlaneTree) :
    build (l++l') ts=build l (build l' ts) := by
  induction l with
  | nil => rfl
  | cons k l ih => simp only [List.cons_append,build,ih]

end PlaneTree
end FKCRT.TreeCoding
end
end OAI
