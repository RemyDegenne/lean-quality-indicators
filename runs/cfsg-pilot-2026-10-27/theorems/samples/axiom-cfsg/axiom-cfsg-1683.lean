public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12
  CFSG.Sporadic.Mathieu CFSG.Blueprint Matrix

namespace Case0M12

theorem m12M_ker {u : Fin 12 → ZMod 2} (hu : ∑ i, u i = 0) (h : m12M *ᵥ u = 0) :
    u = 0 ∨ ∀ i, u i = 1 := by
  choose c hc using m12_D
  have h1 : (1 + m12N * m12M) *ᵥ u = u := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero,
      add_zero]
  have h2 : (1 + m12N * m12M) *ᵥ u = (∑ i, u i * c i) • (fun _ => (1 : ZMod 2)) := by
    conv_lhs => rw [eq_sum_spanVec hu]
    have := map_sum (Matrix.mulVecLin (1 + m12N * m12M)) (fun i => u i • spanVec i) Finset.univ
    simp only [Matrix.mulVecLin_apply] at this
    rw [this]
    funext j
    simp [Finset.sum_apply, Matrix.mulVec_smul, hc, Finset.sum_mul, mul_assoc]
  rw [h1] at h2
  have h3 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h3 (∑ i, u i * c i) with h4 | h4
  · left
    rw [h2, h4, zero_smul]
  · right
    intro i
    rw [h2, h4]
    simp

end Case0M12
end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
end
