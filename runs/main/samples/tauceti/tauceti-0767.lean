public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise TauCeti.ExactDivisor

namespace TauCeti

variable {N Q : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}

theorem Nat.IsExactDivisor.slash_atkinLehnerGL_one (h : 1 ∥ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f) :
    f ∣[k] atkinLehnerGL h.pos (isAtkinLehnerMatrix_atkinLehnerMatrix h) = f := by
  have hM := isAtkinLehnerMatrix_atkinLehnerMatrix h
  obtain ⟨γ, hγM⟩ : ∃ γ : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) = atkinLehnerMatrix N 1 :=
    ⟨⟨atkinLehnerMatrix N 1, by rw [hM.det_eq, Nat.cast_one]⟩, rfl⟩
  have hγ : γ ∈ Gamma0 N := (isAtkinLehnerMatrix_one_iff_mem_Gamma0 γ).mp (hγM ▸ hM)
  have hGL : atkinLehnerGL h.pos hM = mapGL ℝ γ := by
    refine Units.ext ?_
    simp only [coe_atkinLehnerGL, mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hγM]
  rw [hGL]
  exact hf _ (Subgroup.mem_map_of_mem _ hγ)

end TauCeti
end
