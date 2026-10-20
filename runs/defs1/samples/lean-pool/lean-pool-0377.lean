public section

open MeasureTheory

open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Scalar multiplication as a bilinear map on the real vector `L²` space. -/
@[expose]
def allDerivativeScalarVectorActionLinear : ℝ →ₗ[ℝ]
    L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

end CKN.Leray
end
end
