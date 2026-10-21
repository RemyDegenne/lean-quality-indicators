namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

theorem physicalBoxTruncation_of_classify_some (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (c : ∀ i, (P i).Label) (hx : physicalBoxClassify lo N P x = some c) :
    physicalBoxTruncation lo N P hpos q b f x =
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x := by
  by_cases h : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxClassify, dite_eq_left h, Option.some.injEq] at hx
    simp only [physicalBoxTruncation, dite_eq_left h]
    rw [hx]
  · simp only [physicalBoxClassify, dite_eq_right h] at hx
    cases hx

end Erdos3
end
end OAI
