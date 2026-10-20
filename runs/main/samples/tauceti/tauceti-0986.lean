@[expose] public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

theorem not_disjoint_product_univ_pointSet (M : GridState n) {s : Finset (Fin n)}
    (hs : s.Nonempty) : ¬Disjoint (s ×ˢ (Finset.univ : Finset (Fin n))) M.pointSet := by
  rw [M.disjoint_product_pointSet_iff]
  obtain ⟨c, hc⟩ := hs
  exact fun h => h c hc (Finset.mem_univ (M c))

end GridState
end TauCeti
end
