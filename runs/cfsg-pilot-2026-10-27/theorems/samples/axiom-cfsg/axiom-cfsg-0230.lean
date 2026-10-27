public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

open scoped commutatorElement Pointwise

namespace SymThreeCosetData

variable {D : Type*} [Group D] (S : SymThreeCosetData D)

theorem conj_e_one_of_mem_F {f : D} (hf : f ∈ S.F) (B : binarySymMatrices 3) :
    f⁻¹ * S.e B 1 * f = S.e (B + S.ν f) 1 := by
  rw [conj_e, symThreeLinear_one_of_diag_eq_zero _ (S.mem_F.1 hf)]

end SymThreeCosetData
end CFSG.LocalAnalysis.ComponentInitial
end
