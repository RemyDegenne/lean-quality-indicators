public section

noncomputable section

open Set Metric TauCeti

namespace AbstractSimplicialComplex

/-- Reindex the retained simplex coordinates, distinguishing the last coordinate with
`none`. This ambient homeomorphism is shared by the solid and boundary comparisons. -/
def simplexCoordinateReindex (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ₜ (Option (Fin n) → ℝ) :=
  Homeomorph.piCongrLeft (Y := fun _ : Option (Fin n) => ℝ) finSuccEquivLast

end AbstractSimplicialComplex
end
end
