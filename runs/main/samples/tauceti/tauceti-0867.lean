public section

open AlgebraicGeometry CategoryTheory Order

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

theorem relativeDegree_equivCartierDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (f : X ⟶ Y) (D : SchemeWeilDivisor X) :
    Scheme.CartierDivisor.relativeDegree f (equivCartierDivisor hX D) =
      relativeDegree f D := by
  rw [Scheme.CartierDivisor.relativeDegree_apply,
    ← equivCartierDivisor_symm_apply hX, AddEquiv.symm_apply_apply]

end SchemeWeilDivisor
end
end TauCeti.AlgebraicGeometry
end
