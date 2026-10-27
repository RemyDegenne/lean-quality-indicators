namespace P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace A2K1A

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

abbrev ΓtSL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : Subgroup SL(2, ℤ) :=
  CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)

end Group
end A2K1A
end
end P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
