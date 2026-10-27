namespace P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace CohCarrier

namespace BoundaryEisH

p2m_open

section Main

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ} {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A]

variable (δ : SL(2, ℤ)) (h : ℤ) (ε : SL(2, ℤ)) (hε : ε = 1 ∨ ε = -1) (u : ↥(GammaH N H))
  (hu : (u : SL(2, ℤ)) = ε * unipMat (δ 0 0) (δ 1 0) h)

variable (hℓ : ℓ.Prime) (hδ : (ℓ : ℤ) ∣ δ 0 0)

def orbOne (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (u : ↥(GammaH N H)) : OrbQ N H ℓ u :=
  Quotient.mk _ (((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ))

end Main
end BoundaryEisH
end CohCarrier
end P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
