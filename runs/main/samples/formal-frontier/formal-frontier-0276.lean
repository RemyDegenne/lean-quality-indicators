@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UpperTriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

theorem ideal_isHopfIdeal_proof : (ideal K ι).IsHopfIdeal K := by
  let q := quotient K ι
  let comulQuotient : GeneralLinearCoordinateRing.CoordinateRing K ι →ₐ[K]
      CoordinateRing K ι ⊗[K] CoordinateRing K ι :=
    (Algebra.TensorProduct.map q q).comp
      (Bialgebra.comulAlgHom K (GeneralLinearCoordinateRing.CoordinateRing K ι))
  let : CommRing (CoordinateRing K ι ⊗[K] CoordinateRing K ι) := inferInstance
  have counit_gen (i j : ι) :
      (Bialgebra.counitAlgHom K (GeneralLinearCoordinateRing.CoordinateRing K ι))
        (relation K ι i j) = 0 := by
    by_cases hji : j < i
    · simp only [relation, hji, ↓reduceIte]
      change Coalgebra.counit (R := K) (matrix K ι i j) = 0
      rw [native_counit_matrix]
      simp [ne_of_gt hji]
    · simp [relation, hji]
  have comul_gen (i j : ι) : comulQuotient (relation K ι i j) = 0 := by
    by_cases hji : j < i
    · simp only [relation, hji, ↓reduceIte]
      change (Algebra.TensorProduct.map q q)
        (Coalgebra.comul (R := K) (matrix K ι i j)) = 0
      rw [native_comul_matrix, map_sum]
      apply Finset.sum_eq_zero
      intro index _
      rw [Algebra.TensorProduct.map_tmul]
      by_cases hki : index < i
      · rw [quotient_lower K ι i index hki, TensorProduct.zero_tmul]
      · have hjk : j < index := lt_of_lt_of_le hji (le_of_not_gt hki)
        rw [quotient_lower K ι index j hjk, TensorProduct.tmul_zero]
    · simp [relation, hji]
  have antipode_gen (i j : ι) :
      HopfAlgebra.antipode K (relation K ι i j) ∈ ideal K ι := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    by_cases hji : j < i
    · simp only [relation, hji, ↓reduceIte]
      change q (HopfAlgebra.antipode K (matrix K ι i j)) = 0
      have hinv := ((Matrix.GeneralLinearGroup.map q.toRingHom).map_inv
        (GeneralLinearCoordinateRing.universal K ι)).symm
      have hantipode : q (HopfAlgebra.antipode K (matrix K ι i j)) =
          ((universal K ι).1⁻¹ : Matrix.GeneralLinearGroup ι (CoordinateRing K ι)) i j := by
        rw [native_antipode_matrix]
        have heq := congrArg
          (fun g : Matrix.GeneralLinearGroup ι (CoordinateRing K ι) =>
            (g : Matrix ι ι (CoordinateRing K ι)) i j) hinv
        exact heq.symm
      rw [hantipode]
      exact (Matrix.upperTriangularSubgroup ι (CoordinateRing K ι)).inv_mem
        (universal K ι).2 hji
    · simp [relation, hji]
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro x hx
    have h : ideal K ι ≤ RingHom.ker
        (Bialgebra.counitAlgHom K
          (GeneralLinearCoordinateRing.CoordinateRing K ι)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (counit_gen i j)
    change (Bialgebra.counitAlgHom K
      (GeneralLinearCoordinateRing.CoordinateRing K ι)) x = 0
    exact RingHom.mem_ker.mp (h hx)
  · intro x hx
    have h : ideal K ι ≤ RingHom.ker comulQuotient.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (comul_gen i j)
    exact RingHom.mem_ker.mp (h hx)
  · intro x hx
    have h : ideal K ι ≤ (ideal K ι).comap
        (HopfAlgebra.antipodeAlgHom K
          (GeneralLinearCoordinateRing.CoordinateRing K ι)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact antipode_gen i j
    exact h hx

end UpperTriangularCoordinateRing
end
end
