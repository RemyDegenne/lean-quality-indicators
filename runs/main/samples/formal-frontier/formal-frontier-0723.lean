@[expose] public section

set_option warningAsError true

noncomputable section

universe u

namespace DiagonalCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [DecidableEq ι]

theorem ideal_eq_localizedCoordinateIdeal :
    ideal K ι = MvPolynomial.localizedCoordinateIdeal K (diagonalIndices ι)
      (GeneralLinearCoordinateRing.determinant K ι) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    by_cases hij : i = j
    · simp [relation, hij]
    · simp only [relation, hij, ite_false]
      change GeneralLinearCoordinateRing.matrix K ι i j ∈
        MvPolynomial.localizedCoordinateIdeal K (diagonalIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι)
      rw [GeneralLinearCoordinateRing.matrix_apply]
      exact Ideal.subset_span ⟨⟨(i, j), by simpa [diagonalIndices] using hij⟩, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
    have hne : i ≠ j := by simpa [diagonalIndices] using hij
    change GeneralLinearCoordinateRing.matrix K ι i j ∈ ideal K ι
    apply Ideal.subset_span
    exact ⟨(i, j), by simp [relation, hne]⟩

end DiagonalCoordinateRing
end
end
