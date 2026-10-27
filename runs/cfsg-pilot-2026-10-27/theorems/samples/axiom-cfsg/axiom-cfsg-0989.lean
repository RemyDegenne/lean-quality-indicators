public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Subgroup

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Involution

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem tau_fix (A : gsp 2 F) (σ : F ≃+* F) (h : ↥(StatedSp 2 F))
    (hh : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ =
      ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    (conjSp 2 F A * fieldSp 2 F σ) h = h := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_tau, hh, Matrix.mul_assoc]
  have : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
  rw [this, Matrix.mul_one]

end Involution
end CFSG.GH74.Generic
end
