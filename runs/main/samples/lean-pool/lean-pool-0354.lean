@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

open Classical in
theorem blockOddFlagList_key_sorted (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length) :
    List.Pairwise (· ≤ ·)
      ((blockOddFlagList W F v).map
        (fun f => sortKey W f.val)) := by
  have hgen : ∀ (l : List (Fin ((ds W).get v)))
      (H : ∀ j ∈ l, j ∈ oddSlots W F v),
      (l.pmap (fun j hj => (⟨blockFlag W v j,
          (mem_oddSlots j).mp hj⟩ :
            {f : W.Flag // f ∈ F.flags})) H).map
        (fun f => sortKey W f.val) =
      l.map (fun j => sortKey W (blockFlag W v j)) := by
    intro l
    induction l with
    | nil => intro H; rfl
    | cons a t ih =>
      intro H
      rw [List.pmap_cons, List.map_cons, List.map_cons, ih]
  rw [blockOddFlagList, hgen]
  have hsorted := Finset.pairwise_sort
    (r := (· ≤ ·)) (s := oddSlots W F v)
  refine List.Pairwise.map _ ?_ hsorted
  intro a b hab
  rw [sortKey_blockFlag, sortKey_blockFlag]
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact le_of_lt (blockSigmaEquiv_strictMono (ds W) v hlt)
  · rw [heq]

end RS
end
