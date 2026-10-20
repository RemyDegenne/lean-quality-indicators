namespace P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step

set_option autoImplicit false

noncomputable section

namespace StepLineE72

universe u₁ u₂ u₃

section Step

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))

def cls (f : Pt R₀ H L p) (hf : f ∈ K') : V K K' := QuotientGroup.mk ⟨f, hf⟩

end Step
end StepLineE72
end
end P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
