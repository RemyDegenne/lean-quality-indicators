public section

open MeasureTheory

open scoped ENNReal Convolution

open CKN

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The bilinear scalar action on vector-valued functions used by regularized convolution. -/
@[expose]
def regularisedVectorActionLinear : ℝ →ₗ[ℝ] L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

end CKN.Leray
end
end
