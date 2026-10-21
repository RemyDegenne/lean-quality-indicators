namespace OAI

noncomputable section

namespace CKSMixedGeometry

noncomputable section

open CKSCalculus Set Filter

open CKSAngularGeometry (determinant inverse)

open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma tensorEtaField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) (a : A) :
    ContDiffAt ℝ 2 (fun y => tensorEtaField z f y a) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (tensorLapseField_diff hz hf h0 hd).mul ((contDiffAt_pi.mp hf.kb a).sub
    (ContDiffAt.sum fun b _ => (contDiffAt_pi.mp hH b).mul (component_diff (tensorKField_diff hz hf) b a)))

end
end CKSMixedGeometry
end
end OAI
