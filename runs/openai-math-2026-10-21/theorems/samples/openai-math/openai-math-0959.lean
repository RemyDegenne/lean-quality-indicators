namespace OAI

noncomputable section

open Set

open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing

open JetPolynomial (Base)

lemma norm_surfaceJet_operator
    (A : Base →L[ℝ] ProjectionTarget 3)
    (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) (u v : Base)
    (L : Base × ℝ →L[ℝ] ProjectionTarget 3)
    (hL : ∀ w : Base × ℝ, L w = w.2 • A v+B w.1 u) :
    ‖L‖ ≤ ‖A‖*‖v‖+‖B‖*‖u‖ := by
  apply L.opNorm_le_bound (by positivity)
  intro w
  rw [hL]
  have hb : ‖B w.1 u‖ ≤ ‖B‖*‖w.1‖*‖u‖ := by
    calc
      _ ≤ ‖B w.1‖*‖u‖ := (B w.1).le_opNorm _
      _ ≤ (‖B‖*‖w.1‖)*‖u‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
  calc
    _ ≤ ‖w.2 • A v‖+‖B w.1 u‖ := norm_add_le _ _
    _ ≤ ‖w.2‖*(‖A‖*‖v‖)+‖B‖*‖w.1‖*‖u‖ := by
      rw [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)) hb
    _ ≤ ‖w‖*(‖A‖*‖v‖)+‖B‖*‖w‖*‖u‖ := by
      gcongr
      · exact norm_snd_le w
      · exact norm_fst_le w
    _ = _ := by ring

end ClosedSurfaceR4.FiniteOrderSmoothing
end
end OAI
