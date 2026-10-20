@[expose] public section

variable {ι : Sort*} {F α β : Type*}

open Finset OrderDual

section Lattice

variable {ι : Sort*} [Lattice α] [Lattice β] {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}

open Set

lemma IsSublattice.preimage [FunLike F β α] [LatticeHomClass F β α]
    (hs : IsSublattice s) (f : F) :
    IsSublattice (f ⁻¹' s) := ⟨hs.1.preimage _, hs.2.preimage _⟩

end Lattice
end
