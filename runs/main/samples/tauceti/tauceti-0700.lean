public noncomputable section

open UpperHalfPlane Complex Filter Function Metric Set SlashInvariantForm Periodic

open scoped ModularForm Topology Filter Manifold

namespace TauCeti

variable {h : ℝ} {g : ℍ → ℂ}

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F}

@[simp]
lemma orderAtCusp_pos_iff [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : 2 * h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    0 < orderAtCusp h ⇑f ↔ cuspFunction (2 * h) ⇑f 0 = 0 := by
  rw [orderAtCusp_def]
  rw [div_pos_iff_of_pos_right (by norm_num : (0 : ℚ) < 2), Int.cast_pos]
  exact qExpansionOrderAtCusp_pos_iff (by positivity) hΓ hf

end ModularForm
end TauCeti
end
