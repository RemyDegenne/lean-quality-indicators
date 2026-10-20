public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

theorem hungerbuhlerWasem_residueTheorem_of_simple_poles {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (S : Finset ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSU : (S : Set ℂ) ⊆ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) :=
  hungerbuhlerWasem_residueTheorem hU S γ a b hγ_imm hSU hclosed hγa hγU hf hmero hnull
    (conditionAprime_of_simple_poles hU hγ_imm
      (by rcases le_total a b with h | h
          · rwa [min_eq_left h]
          · rwa [min_eq_right h, ← hclosed]) hγU hf h_simple)
    (conditionB_of_simple_poles hU hγU hf h_simple)

end TauCeti.Contour
end
end
