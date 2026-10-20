public section

namespace TauCeti

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-- Reverse the orientation while retaining the base point. The traversal order is reversed,
crossing signs and over/under statuses are preserved, and the partner matching is conjugated by
the reversal of the visit indices. -/
def reverse (D : BasedOrientedGaussCode n) : BasedOrientedGaussCode n where
  visit := D.visit ∘ Fin.rev
  over := D.over ∘ Fin.rev
  sign := D.sign
  partner := PerfectMatching.congr Fin.revPerm D.partner
  visit_eq_iff := by
    intro i j
    constructor
    · intro h
      rcases (D.visit_eq_iff (Fin.rev i) (Fin.rev j)).mp h with h | h
      · exact Or.inl (Fin.rev_injective h)
      · exact Or.inr (by simpa using congrArg Fin.rev h)
    · rintro (h | h)
      · apply (D.visit_eq_iff (Fin.rev i) (Fin.rev j)).mpr
        exact Or.inl (congrArg Fin.rev h)
      · apply (D.visit_eq_iff (Fin.rev i) (Fin.rev j)).mpr
        exact Or.inr (by simpa using congrArg Fin.rev h)
  over_partner := by
    intro i
    simp [Function.comp_def]

end BasedOrientedGaussCode
end TauCeti
end
