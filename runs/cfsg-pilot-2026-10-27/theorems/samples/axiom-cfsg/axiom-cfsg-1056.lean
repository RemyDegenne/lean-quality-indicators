public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open

open CFSG.ClassicalInvolution.Phan

open Matrix

variable {k : ℕ} {K : Type} [Field K]

theorem exists_sl2_diagonal {b : K} (hb : b ≠ 0) :
    ∃ D : Matrix.SpecialLinearGroup (Fin 2) K,
      (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![b, b⁻¹] :=
  ⟨⟨Matrix.diagonal ![b, b⁻¹], by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp [hb]⟩, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
end
