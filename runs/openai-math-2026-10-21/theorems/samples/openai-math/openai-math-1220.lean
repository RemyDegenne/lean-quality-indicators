namespace OAI

section

section

open scoped symmDiff

namespace SimpleAmenable

open scoped commutatorElement

open scoped commutatorElement

section WindowRectangles

theorem windowRectangle_cover {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ)
    (p : GenericSquare a) : ∃ i : Fin 2 → Fin n, p ∈ (windowRectangle a n q i).val := by
  have hh (j : Fin 2) := windowCell_cover (a := a) j n hn (q j) p
  choose i hi using hh
  refine ⟨i,hi 0,hi 1⟩

end WindowRectangles
end SimpleAmenable
end
end
end OAI
