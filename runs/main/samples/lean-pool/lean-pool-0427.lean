@[expose] public section

open scoped PowerSeries.WithPiTopology

namespace FerrersDiagram

variable {n : ℕ}

theorem sum_unfoldDelta {l : List ℕ} (hsort : l.Pairwise (· ≥ ·)) :
    (((unfoldDelta l).zipIdx 1).map fun p ↦ p.1 * p.2).sum = l.sum :=
match l with
| [] | [x] => by simp [unfoldDelta]
| x :: y :: xs => by
  rw [List.pairwise_cons_cons_iff_of_trans] at hsort
  rw [unfoldDelta, List.sum_cons, List.zipIdx_cons, List.map_cons, List.sum_cons, List.zipIdx_succ,
    ← sum_unfoldDelta hsort.2, mul_one, List.map_map]
  simp only
  have : (fun x ↦ x.1 * x.2) ∘ (fun (x : ℕ × ℕ) ↦ (x.1, x.2 + 1)) =
      fun x ↦ x.1 + x.1 * (x.2) := by
    ext x
    simp
    ring
  rw [this, List.sum_map_add, ← add_assoc]
  suffices x - y + (unfoldDelta (y :: xs)).sum = x by simpa
  rw [← Nat.sub_add_comm hsort.1.le]
  apply Nat.sub_eq_of_eq_add
  rw [Nat.add_left_cancel_iff, sum_unfoldDelta' hsort.2]
  simp

end FerrersDiagram
end
