@[expose] public section

noncomputable section

namespace ToricIdeals.SplitQuadric

theorem existsUnique_reduced_preimage_iff (n : Fin 3 →₀ ℕ) :
    (∃! m : Fin 4 →₀ ℕ, Reduced m ∧ exponentMap m = n) ↔ n 2 ≤ n 0 + n 1 := by
  constructor
  · rintro ⟨m, ⟨_, h⟩, _⟩
    exact (mem_mrange_iff n).1 (AddMonoidHom.mem_mrange.mpr ⟨m, h⟩)
  · intro hn
    refine ⟨normal n, ⟨normal_reduced n, exponentMap_normal n hn⟩, ?_⟩
    intro m hm
    exact eq_of_reduced_of_exponentMap_eq hm.1 (normal_reduced n)
      (hm.2.trans (exponentMap_normal n hn).symm)

end ToricIdeals.SplitQuadric
end
end
