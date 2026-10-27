public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem closure_planeFixU_heis_inner (hcore : UnitaryHeisCore) (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {x y : GL (Fin 3) K}
    (hx : x ∈ primeFormUnitary h (idGram K 3)) (hy : y ∈ primeFormUnitary h (idGram K 3))
    {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hxy : (x : Matrix (Fin 3) (Fin 3) K) * y = ω • ((y : Matrix (Fin 3) (Fin 3) K) * x))
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) :
    Subgroup.closure (planeFixU ℓ f K x y) = ⊤ := by
  obtain ⟨P, ξ, hPU, hξ3, hXP, hYP⟩ := exists_unitary_heisenberg_basis_alpha h hq3 hy hx hω hxy
    hx3 (α := 1) (by rw [hy3, one_smul])
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hDξ : (diagonal ![ξ, ξ * ω, ξ * ω ^ 2] : Matrix (Fin 3) (Fin 3) K) = ξ • hD ω := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, mul_comm]
  rw [hDξ] at hXP
  have hYP' : (y : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * hS := hYP
  set Pu : primeFormUnitary h (idGram K 3) := ⟨P, hPU⟩ with hPu
  have hcl := hcore ℓ f K h hq3 hq ω hω
  refine eq_top_of_conj_closure h Pu hcl ?_
  rintro g ⟨M, hM, hgM⟩
  refine Subgroup.subset_closure ?_
  have hPm : ((Pu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) := rfl
  have hgM' : g ∈ FixU ℓ f K M := hgM
  simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl (mem_FixU_conj h Pu (by rw [hPm]; exact hXP)
      ((mem_FixU_smul hξ0).2 hgM'))))
  · exact Or.inl (Or.inl (Or.inr (mem_FixU_conj h Pu (by rw [hPm]; exact hYP') hgM')))
  · refine Or.inl (Or.inr (mem_FixU_conj h Pu (by
      rw [hPm, Units.val_mul]; exact intertwine_mul_right hXP hYP') ?_))
    rw [Matrix.smul_mul]; exact (mem_FixU_smul hξ0).2 hgM'
  · refine Or.inr (mem_FixU_conj h Pu (by
      rw [hPm, Units.val_mul, Units.val_pow_eq_pow_val]
      exact intertwine_mul_right hXP (intertwine_pow_right hYP' 2)) ?_)
    rw [pow_two, Matrix.smul_mul, ← Matrix.mul_assoc]
    exact (mem_FixU_smul hξ0).2 hgM'

end CFSG.LieType.SeitzGeneration
end
