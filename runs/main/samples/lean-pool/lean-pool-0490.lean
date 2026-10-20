@[expose] public section

open Metric Set

open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

theorem exists_lists_of_isPolygonal : ∀ {L : List (Set Plane)}, (∀ A ∈ L, IsPolygonal A) →
    ∃ M : List (List Plane), (⋃ vs ∈ M, poly vs) = ⋃ A ∈ L, A
  | [], _ => ⟨[], by simp⟩
  | A :: L, h => by
    obtain ⟨vs, rfl⟩ := h A (List.mem_cons_self ..)
    obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal fun B hB => h B (List.mem_cons_of_mem _ hB)
    refine ⟨vs :: M, ?_⟩
    rw [biUnion_list_cons (fun ws : List Plane => poly ws),
      biUnion_list_cons (fun B : Set Plane => B), hM]

end Schoenflies
end
