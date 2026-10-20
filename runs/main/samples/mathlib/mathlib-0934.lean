@[expose] public section

namespace Set

variable {α β : Type*} {s t : Set α}

section Lattice

theorem Finite.finite_of_encard_le {s : Set α} {t : Set β} (hs : s.Finite)
    (h : t.encard ≤ s.encard) : t.Finite :=
  encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

end Lattice
end Set
end
