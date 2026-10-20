public section

namespace TauCeti

universe u v v' w w'

variable {A : Type u} [Ring A]

variable {M : Type v} [AddCommGroup M] [Module A M]

variable {M' : Type v'} [AddCommGroup M'] [Module A M']

variable {N : Type w} [AddCommGroup N] [Module A N]

variable {N' : Type w'} [AddCommGroup N'] [Module A N']

/-- The number of members of the finite set of submodules `s` that are copies of `N`.  When `s` is
a decomposition of `M` into indecomposable submodules this is the multiplicity of `N` in `M`, by
`TauCeti.decompositionMultiplicity_eq_indecomposableMultiplicity`. -/
noncomputable def decompositionMultiplicity (s : Finset (Submodule A M)) (N : Type w)
    [AddCommGroup N] [Module A N] : ℕ :=
  Nat.card {P : Submodule A M // P ∈ s ∧ Nonempty (↥P ≃ₗ[A] N)}

end TauCeti
end
