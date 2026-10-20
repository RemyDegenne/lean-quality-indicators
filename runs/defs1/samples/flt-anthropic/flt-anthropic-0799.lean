namespace P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two

attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

set_option maxHeartbeats 3200000

open scoped Pointwise

p2m_reactivate

noncomputable section

namespace P2MMultOR

open P2MMultO

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def decRingEquiv : ↥(decDVR A) ≃+* ↥(decRing A) where
  toFun z := ⟨val z, mem_decRing_iff.mpr ⟨val_memA z, (z : decField A).2⟩⟩
  invFun x := ⟨⟨(x : ℚ̄), (mem_decRing_iff.mp x.2).2⟩, (ValuationSubring.mem_comap).mpr (mem_decRing_iff.mp x.2).1⟩
  left_inv z := rfl
  right_inv x := rfl
  map_mul' a b := Subtype.ext (val_mul a b)
  map_add' a b := Subtype.ext (val_add a b)

end P2MMultOR
end
end P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two
