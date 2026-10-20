@[expose] public section

namespace Finset

variable {α β : Type*}

variable {s t : Finset α} {a b : α}

section Sym

variable [DecidableEq α] {n : ℕ}

theorem sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m ∈ s.sym (n - i)) :
    m.fill a i ∈ (insert a s).sym n :=
  mem_sym_iff.2 fun b hb ↦
    mem_insert.2 <| (Sym.mem_fill_iff.1 hb).imp And.right <| mem_sym_iff.1 h b

end Sym
end Finset
end
