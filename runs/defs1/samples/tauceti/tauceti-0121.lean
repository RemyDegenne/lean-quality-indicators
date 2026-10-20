public section

namespace TauCeti.DynkinType

open Set Submodule

open scoped symmDiff

/-- **The `i`-th simple reflection of type `Dₙ`, acting on the sign sets that index the spin
basis.**

A sign is recorded by membership in the finset. At a chain node `i`, whose simple root is
`eᵢ - eᵢ₊₁`, the reflection exchanges the signs at `i` and `i + 1`. At the terminal fork node,
whose simple root is `e_{n-2} + e_{n-1}`, it exchanges the last two signs and reverses both. -/
def typeDSpinReflection {n : ℕ} (i : Fin n) (s : Finset (Fin n)) : Finset (Fin n) :=
  if h : (i : ℕ) + 1 < n then
    s.map (Equiv.swap i ⟨(i : ℕ) + 1, h⟩).toEmbedding
  else
    s.map (Equiv.swap (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) i).toEmbedding ∆
      {(⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n), i}

end TauCeti.DynkinType
end
