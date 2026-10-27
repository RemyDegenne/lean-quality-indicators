namespace P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

open UpperHalfPlane

noncomputable section

namespace P2mSolLevelOneEsymm

section FormalModel

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

variable (p : ℕ) [hp : Fact p.Prime] (B : PowerSeries ℤ)

noncomputable def zetaO : OO := ⟨zeta p, (zeta_prim p).isIntegral (Fact.out : p.Prime).pos⟩

end FormalModel
end P2mSolLevelOneEsymm
end
end P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
