namespace OAI

section

namespace Erdos3

open RealInnerProductSpace

theorem abs_coordinate_det_le_sqrt_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (v : Fin r → EuclideanSpace ℝ ι) (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => v i (p j))).det| ≤ Real.sqrt (Matrix.gram ℝ v).det := by
  classical
  let e : Fin r → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single (p i) 1
  let u := exteriorPower.ιMulti ℝ r e
  let w := exteriorPower.ιMulti ℝ r v
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp p hp
  have hgram : Matrix.gram ℝ e = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr he
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r e) = 1
      rw [exteriorPower.inner_ιMulti_self, hgram, Matrix.det_one]
    nlinarith [norm_nonneg u]
  have hi : inner ℝ u w = (Matrix.of (fun i j => v i (p j))).det := by
    change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r v) = _
    rw [exteriorPower.inner_ιMulti_ιMulti]
    congr 1
    ext i j
    simp [e, EuclideanSpace.inner_single_left]
  have h := abs_real_inner_le_norm u w
  rw [hi, hu, one_mul] at h
  exact h.trans_eq (exterior_norm_eq_sqrt_gram v)

end Erdos3
end
end OAI
