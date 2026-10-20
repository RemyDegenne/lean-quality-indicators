set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}

variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

variable (𝒞 : SemistableCovering q M' A W)

theorem teleSrc_ne_teleTgt (e : Fin 𝒞.teleM) : 𝒞.teleSrc e ≠ 𝒞.teleTgt e := fun h =>
  Sum.inl_ne_inr (𝒞.eIdx.injective h)

end ModularCurve.FullLevel.SemistableCovering
end
