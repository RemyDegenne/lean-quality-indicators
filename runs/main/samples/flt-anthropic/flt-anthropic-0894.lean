namespace P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two

attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

set_option maxHeartbeats 3200000

open scoped Pointwise

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

namespace P2MMultE

open scoped TensorProduct

p2m_reactivate

section Facade

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]

variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]

variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]

variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

scoped instance instModuleFiniteES (h : IPtHyp S) : Module.Finite O ↥(ES h) := flatClosure_finite _

scoped instance instModuleFreeES (h : IPtHyp S) : Module.Free O ↥(ES h) := flatClosure_free _

scoped instance instModuleFlatES (h : IPtHyp S) : Module.Flat O ↥(ES h) := flatClosure_flat _

theorem galE_eq_self_iff (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) :
    galE h σ ψ = ψ ↔ ∀ e, σ (ψ.ofConv e) = ψ.ofConv e := by
  constructor
  · intro hfix e
    rw [← galE_apply h σ ψ e, hfix]
  · intro hfix
    rw [← toConv_ofConv (galE h σ ψ), ← toConv_ofConv ψ]
    congr 1
    exact AlgHom.ext hfix

end Facade
end P2MMultE
end P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two
