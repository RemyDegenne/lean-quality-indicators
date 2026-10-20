@[expose] public section

namespace Utilities.Certificate.CubicMatrixReplay

open Utilities.Certificate

open Utilities

open Utilities.Certificate.CubicMatrixReplay

open Utilities.Certificate.CubicMatrixReplay

open ExplicitPotential

theorem weightKey_swap (n k : ℕ) (hk : k + 1 < n) (F G : ℕ → ℕ)
    (hOther : ∀ j, j < n → j ≠ k → j ≠ k + 1 → G j = F j)
    (hAt : G k = F (k + 1)) (hAt' : G (k + 1) = F k) :
    (F (k + 1) < F k → weightKey n G < weightKey n F) ∧
      (F k = F (k + 1) → weightKey n G = weightKey n F) := by
  classical
  have hRest : (∑ j ∈ Finset.range n \ {k, k + 1}, (n - j) * G j)
      = ∑ j ∈ Finset.range n \ {k, k + 1}, (n - j) * F j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_sdiff, Finset.mem_range] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [hOther j hj.1 hj.2.1 hj.2.2]
  have hPair : G k + G (k + 1) = F k + F (k + 1) := by
    rw [hAt, hAt']; exact Nat.add_comm _ _
  rw [weightKey_split n k hk F, weightKey_split n k hk G, hRest, hPair, hAt]
  refine ⟨fun hLt => ?_, fun hEq => ?_⟩
  · exact Nat.add_lt_add_left (Nat.add_lt_add_left hLt _) _
  · rw [hEq]

end Utilities.Certificate.CubicMatrixReplay
end
