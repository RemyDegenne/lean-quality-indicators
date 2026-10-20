@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [DecidableEq ι] (R : Type u) [CommRing R]

namespace DiagonalGroup

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

variable {R S : Type u} [CommRing R] [CommRing S]

@[ext] theorem ext {g h : DiagonalGroup ι R}
    (heq : ∀ i, g.1 i i = h.1 i i) : g = h := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    exact heq i
  · exact (g.2 i j hij).trans (h.2 i j hij).symm

end DiagonalGroup
end Matrix
end
end
