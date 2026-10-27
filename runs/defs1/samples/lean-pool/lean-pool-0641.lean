@[expose] public section

universe u

namespace FirstOrder.Combinatorics.PairERGen

section TreeSkeleton

variable {κ : Cardinal.{0}} {C : Type}

/-- The successor set `S(h)`: points above all the reps respecting the recorded
colors. (`β.ToType`-indexed `validFiber` shape, with a plain-function `rep`.) -/
def ehmrFiber (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (rep : β.ToType → Source κ) (col : EHMRNodeAt C β) : Set (Source κ) :=
  { y | ∀ x : β.ToType, ∃ h : rep x < y, cR (pairEmbed h) = col x }

end TreeSkeleton
end FirstOrder.Combinatorics.PairERGen
end
