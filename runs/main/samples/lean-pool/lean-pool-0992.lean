@[expose] public section

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

theorem edgeSumWithin_erase [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    edgeSumWithin G S = edgeSumWithin G (S.erase v) + 2 * degWithin G S v := by
  have hstep : ∀ u : V, degWithin G S u
      = degWithin G (S.erase v) u + (if G.Adj u v then 1 else 0) := by
    intro u
    rw [degWithin, degWithin]
    have hS : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    nth_rewrite 1 [hS]
    rw [Finset.filter_insert]
    by_cases hadj : G.Adj u v
    · have hvnotin : v ∉ (S.erase v).filter (fun w => G.Adj u w) := by
        simp [Finset.mem_filter, Finset.mem_erase]
      rw [ite_eq_left hadj, Finset.card_insert_of_notMem hvnotin, ite_eq_left hadj]
    · rw [ite_eq_right hadj, ite_eq_right hadj, add_zero]
  have hcount : ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℕ) else 0) = degWithin G S v := by
    have h1 : ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℕ) else 0)
        = ∑ u ∈ S, (if G.Adj u v then (1 : ℕ) else 0) :=
      Finset.sum_erase (f := fun u => if G.Adj u v then (1 : ℕ) else 0) (a := v) S
        (by simp [SimpleGraph.irrefl])
    rw [h1, degWithin, Finset.card_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    exact if_congr (G.adj_comm u v) rfl rfl
  rw [edgeSumWithin, ← Finset.add_sum_erase _ _ hv]
  rw [Finset.sum_congr rfl (fun u _ => hstep u)]
  rw [Finset.sum_add_distrib, hcount, edgeSumWithin]
  omega

end ACMax
end
