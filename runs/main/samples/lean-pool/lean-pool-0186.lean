@[expose] public section

namespace BollobasNikiforov

open Function Matrix Set

open scoped Matrix

noncomputable section

@[simp] lemma cVec_two (ti x : ℝ) : cVec ti x 2 = truncSq ti x := by
  simp [cVec, cons_val_two, vecHead, vecTail]

end
end BollobasNikiforov
end
