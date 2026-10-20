namespace P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step

set_option autoImplicit false

noncomputable section

namespace StepLineE72

universe u₁ u₂ u₃

section Line

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))
  {Γ : Type*} [Group Γ] (τ : Γ →* (L →ₐ[R₀] L))
  (hK : ∀ γ : Γ, ∀ f ∈ K, postComp (p := p) (τ γ) f ∈ K)
  (hK' : ∀ γ : Γ, ∀ f ∈ K', postComp (p := p) (τ γ) f ∈ K')

theorem act_add (a b : Comm K K' τ hK hK') (f : Pt R₀ H L p) (hf : f ∈ K') :
    ∃ k ∈ K, act K K' τ hK hK' (a + b) f = act K K' τ hK hK' a f * act K K' τ hK hK' b f * k := by
  have ha := act_mem K K' τ hK hK' a f hf
  have hb := act_mem K K' τ hK hK' b f hf
  have h1 := ofMul_cls_act K K' τ hK hK' a f hf
  have h2 := ofMul_cls_act K K' τ hK hK' b f hf
  have h3 := ofMul_cls_act K K' τ hK hK' (a + b) f hf
  apply exists_mul_of_cls_eq K K' (K'.mul_mem ha hb) (act_mem K K' τ hK hK' (a + b) f hf)
  rw [cls_mul K K' ha hb, ofMul_mul, h1, h2, h3, Subalgebra.coe_add, LinearMap.add_apply]

end Line
end StepLineE72
end
end P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
