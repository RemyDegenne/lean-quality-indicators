namespace P2MW.S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three

attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow

set_option autoImplicit false

open CongruenceSubgroup CuspidalType

open scoped MatrixGroups

namespace K3a3Chi

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

variable {κ : Type} [Field κ] {W : Type} [AddCommMonoid W] [Module κ W]

noncomputable abbrev adj (X : Representation κ (CuspidalType.GL2 q) W) (ℓ : ℕ) : W →ₗ[κ] W :=
  if h : ((ℓ : ZMod q) ≠ 0) then X (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id

end K3a3Chi
end P2MW.S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
