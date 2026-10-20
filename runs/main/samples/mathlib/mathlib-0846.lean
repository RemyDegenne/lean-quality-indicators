@[expose] public section

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}

variable {a b v : α} {p : G.Walk a b} {f : G →g H}

variable [Fintype α]

lemma IsHamiltonian.exists_isHamiltonianCycle [Nontrivial α] (hG : G.IsHamiltonian) (v : α) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  obtain ⟨u, p, hp⟩ := hG Fintype.one_lt_card.ne'; exact ⟨p.rotate v <| hp.mem_support _, by simpa⟩

end SimpleGraph
end
