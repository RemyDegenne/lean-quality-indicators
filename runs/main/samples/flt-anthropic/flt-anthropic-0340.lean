namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero_bare

set_option autoImplicit false

p2m_open

open scoped Quaternion TensorProduct NumberField

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open AlgebraicGeometry.SmallExtension

namespace P2mWs2RG2

section Frame

variable {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
  (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
  (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover)
  (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
  (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
  (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)

include hτB in
theorem ρ_over (r : 𝒰.Idx 2) (ℓ : Fin 3) :
    ρ hπ hker D₀ 𝒰 τ hτg r ℓ ≫ (𝒰.inter r).ι ≫ D₀.f = (𝒰.inter r).ι ≫ D₀.f := by
  rw [ρ_ι_assoc, hτB, Scheme.homOfLE_ι_assoc]

end Frame
end P2mWs2RG2
end P2MW.S_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero_bare
