open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

def IsInvertible (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U)), x ∈ X.basicOpen f ∧
    ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f), I.ideal (X.affineBasicOpen f) = Ideal.span {g}

end AlgebraicGeometry.Scheme.IdealSheafData
