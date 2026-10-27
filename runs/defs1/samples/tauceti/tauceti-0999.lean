public section

open Subgroup

open scoped commutatorElement

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Deviation

variable (θ : G →* G) (hθc : Continuous θ) {m : ℕ}
  (hθ : ∀ g, g⁻¹ * θ g ∈ pLowerCentralSeries p G m)

/-- **The graded deviation** `D_k : gr_k(G) →+ gr_{m+k}(G)` of an endomorphism `θ` congruent to
the identity modulo `λ_m`: the map induced by `g ↦ g⁻¹ * θ g`. Its defining equation is
`TauCeti.gradedDeviation_gradedMk`. For `m ≥ 1` it is a derivation of the graded structure
(`TauCeti.gradedDeviation_gradedBracket`), compatible with `π` away from degree zero
(`TauCeti.gradedDeviation_gradedPow_of_one_le`) and with the binomial defect
`(p choose 2) • [D x, x]` in degree zero (`TauCeti.gradedDeviation_gradedPow_zero`). -/
def gradedDeviation (k : ℕ) : gradedPiece p G k →+ gradedPiece p G (m + k) :=
  MonoidHom.toAdditive
    (QuotientGroup.lift _ (deviationAux θ hθc hθ k) (subgroupOf_le_ker_deviationAux θ hθc hθ k))

end Deviation
end TauCeti
end
