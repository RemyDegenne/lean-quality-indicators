@[expose] public section

open FunctionField

open FunctionField.Chart

open scoped Polynomial RatFunc nonZeroDivisors

namespace WeierstrassCurve.Affine.Chart

noncomputable section

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]

variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]

local instance instDecidableEqRiemannRoch : DecidableEq k := Classical.decEq k

namespace Internal

omit [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
@[simp]
lemma finitePart_apply (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    finitePart (k := k) K D v = D (Sum.inl v) := rfl

end Internal
end
end WeierstrassCurve.Affine.Chart
end
