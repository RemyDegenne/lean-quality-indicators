@[expose] public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

namespace LeftOrdContinuous

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

@[to_dual]
theorem map_sSup' (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) :
    f (sSup s) = sSup (f '' s) :=
  (hf hs <| isLUB_sSup s).sSup_eq.symm

end CompleteLattice
end LeftOrdContinuous
end
