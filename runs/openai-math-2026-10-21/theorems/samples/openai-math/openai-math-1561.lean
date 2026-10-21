namespace OAI

namespace CommonBasesFPRAS

section

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

section

open scoped BigOperators Classical

variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (hN : 0<N)

include hN in
lemma historySample_length_le (h : List (PhaseSample n N)) (j : ℕ) :
    (historySample (observedSets n N) h j).length≤N := by
  unfold historySample
  generalize hget : h[j]?=x
  cases x with
  | none => simp
  | some x => simpa only [Option.map_some,Option.getD_some] using (observedSets_length n N hN x).le

end
end
end CommonBasesFPRAS
end OAI
