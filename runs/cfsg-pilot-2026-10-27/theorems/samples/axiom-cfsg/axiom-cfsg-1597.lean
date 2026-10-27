public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj

open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd)

variable {K : Type} [Field K] {d : ℕ}

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem conj_mul_conj {X N : Matrix (Fin d) (Fin d) K} (S : GL (Fin d) K) (h : X * N = N) :
    ((S : Matrix (Fin d) (Fin d) K) * X * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S : Matrix (Fin d) (Fin d) K) * N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      (S : Matrix (Fin d) (Fin d) K) * N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have e : ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (S : Matrix (Fin d) (Fin d) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((S : Matrix (Fin d) (Fin d) K) * X * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S : Matrix (Fin d) (Fin d) K) * N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      (S : Matrix (Fin d) (Fin d) K) * X *
        (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (S : Matrix (Fin d) (Fin d) K)) *
          N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one, Matrix.mul_assoc (S : Matrix (Fin d) (Fin d) K) X N, h]

end CFSG.ComponentClassification.GSThmB.QPUCl
end
