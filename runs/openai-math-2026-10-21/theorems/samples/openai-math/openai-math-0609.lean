namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation

open scoped Classical BigOperators

open ChainSubdivision BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

section

local instance : DecidableEq Types.Letter := Classical.decEq _

variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]

variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

theorem label_union_mean {Ω W : Type*} (sample : Finset Ω) (labels : Finset W)
    (X : W → Ω → ℕ) (B : ℝ)
    (hX : ∀ w ∈ labels, ((∑ r ∈ sample, X w r : ℕ) : ℝ)/sample.card ≤ B) :
    ((∑ r ∈ sample, ∑ w ∈ labels, X w r : ℕ) : ℝ)/sample.card ≤
      (labels.card : ℝ)*B := by
  rw [Finset.sum_comm,Nat.cast_sum,Finset.sum_div]
  calc
    _ ≤ ∑ _w ∈ labels, B := Finset.sum_le_sum hX
    _ = _ := by simp

end
end TorsionFreeZeroDivisors.StageExpectation
end
end OAI
