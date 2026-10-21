namespace OAI

section

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

namespace ExactQuantumFactoring.AuxiliaryTree

lemma completed_children {m n a b : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (ha : a∈seen [m] (2*n^2)) (hc : b∈children a) : b∈seen [m] (2*n^2) := by
  have h:=children_covered [m] (2*n^2) ha hc
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h

end ExactQuantumFactoring.AuxiliaryTree
end
end OAI
