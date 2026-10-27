public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix

open scoped MatrixGroups

open GenLocU4Basic GenLocU4Out GenLocU4Gen CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary GenLocU4OutDaRot

namespace GenLocU4OutDaCore

section Generic

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem herm_mixed_iso {ι κ : K} (hι : ι * ι = -1) (hσι : σ ι = ι) (hκ : κ + σ κ = 0) :
    herm σ (![1 + κ, ι * (1 - κ)] : Fin 2 → K) ![1 + κ, ι * (1 - κ)] = 0 ∧
      herm σ (![1 + κ, ι * (1 - κ), 0, 0] : Fin 4 → K) ![1 + κ, ι * (1 - κ), 0, 0] = 0 := by
  constructor
  · rw [herm_def, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_one, map_mul, map_sub, hσι]
    linear_combination 2 * hκ + ((1 - σ κ) * (1 - κ)) * hι
  · rw [herm_def, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, map_add, map_one, map_mul, map_sub, map_zero, hσι]
    linear_combination 2 * hκ + ((1 - σ κ) * (1 - κ)) * hι

end Generic
end GenLocU4OutDaCore
end CFSG.GH74.Generic.BProg.B2
end
