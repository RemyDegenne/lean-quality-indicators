public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.S1.Uni Matrix

namespace GenLocU4OutFrDb

open GenLocU4Basic GenLocU4Out

variable {p f : ℕ} {K : Type} [Field K]

theorem comm_aux (h : UnitaryFieldData p f K) {x B P : Matrix (Fin 4) (Fin 4) K} {σ : Fin 4 → K}
    (hP : cT h P * P = 1) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (hxP : x * P = P * Matrix.diagonal σ)
    (hxB : x * B = B * x.map h.bar) :
    Matrix.diagonal σ * (cT h P * B * P.map h.bar) = (cT h P * B * P.map h.bar) * Matrix.diagonal σ := by
  have hP' : P * cT h P = 1 := mul_eq_one_comm.mp hP
  have e1 : cT h P * x = Matrix.diagonal σ * cT h P := by
    calc cT h P * x = cT h P * x * (P * cT h P) := by rw [hP', Matrix.mul_one]
      _ = cT h P * (x * P) * cT h P := by simp only [Matrix.mul_assoc]
      _ = cT h P * (P * Matrix.diagonal σ) * cT h P := by rw [hxP]
      _ = (cT h P * P) * Matrix.diagonal σ * cT h P := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal σ * cT h P := by rw [hP, Matrix.one_mul]
  have e2 : x.map h.bar * P.map h.bar = P.map h.bar * Matrix.diagonal σ := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) hxP
    simp only [Matrix.map_mul] at this
    rw [bar_diagonal h hσ] at this
    exact this
  calc Matrix.diagonal σ * (cT h P * B * P.map h.bar)
      = (Matrix.diagonal σ * cT h P) * B * P.map h.bar := by simp only [Matrix.mul_assoc]
    _ = (cT h P * x) * B * P.map h.bar := by rw [e1]
    _ = cT h P * (x * B) * P.map h.bar := by simp only [Matrix.mul_assoc]
    _ = cT h P * (B * x.map h.bar) * P.map h.bar := by rw [hxB]
    _ = cT h P * B * (x.map h.bar * P.map h.bar) := by simp only [Matrix.mul_assoc]
    _ = cT h P * B * (P.map h.bar * Matrix.diagonal σ) := by rw [e2]
    _ = (cT h P * B * P.map h.bar) * Matrix.diagonal σ := by simp only [Matrix.mul_assoc]

end GenLocU4OutFrDb
end CFSG.GH74.Generic.BProg.B2
end
