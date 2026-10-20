public section

noncomputable section

open ModularForm UpperHalfPlane Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open EisensteinSeries

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {u v : ℕ} (N : ℕ) (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

variable {N}

variable {k : ℤ}

theorem weightedEisensteinSeries_charWeight_slash [NeZero N] (huv : u * v ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    weightedEisensteinSeries (charWeight N ψ φ) k ∣[k] γ =
      (ψ (γ 1 1 : ZMod u) * φ (γ 1 1 : ZMod v)) •
        weightedEisensteinSeries (charWeight N ψ φ) k := by
  rw [weightedEisensteinSeries_slash_apply, ← weightedEisensteinSeries_smul]
  congr 1
  ext a
  obtain ⟨x, rfl⟩ : ∃ x : Fin 2 → ℤ, (↑) ∘ x = a := ⟨fun i ↦ ((a i).val : ℤ), by ext i; simp⟩
  rw [← intCast_comp_vecMul, charWeight_vecMul_inv ψ φ huv hγ, Pi.smul_apply, smul_eq_mul]

end TauCeti.EisensteinSeries
end
end
