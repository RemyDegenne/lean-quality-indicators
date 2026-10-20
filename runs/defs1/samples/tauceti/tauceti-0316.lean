public section

open Module

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}

variable [Field k] [Field k'] [Field F] [Field F']

variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']

variable [IsScalarTower k k' F'] [IsScalarTower k F F']

variable [Algebra.IsSeparable k k']

section FiniteFibres

variable [Algebra.IsIntegral F F']

variable [∀ P : Place k F, Finite {P' : Place k' F' // P'.restrict k F = P}]

/-- **A basis of `L(D)` is a basis of `L(Con D)`** (Stichtenoth, Theorem 3.6.3(d)): in an
algebraic separable constant field extension, the image of a `k`-basis of `L(D)` is a
`k'`-basis of the Riemann–Roch space of the conorm of `D`. -/
noncomputable def riemannRochSpaceConormBasis (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF : IsFunctionField k F) (D : Divisor k F)
    {ι : Type*} (b : Basis ι k (riemannRochSpace D)) :
    Basis ι k' (riemannRochSpace (Divisor.conorm k' F' D)) :=
  (Basis.span (linearIndependent_algebraMap_riemannRochSpace hex b)).map
    (LinearEquiv.ofEq _ _ (span_range_algebraMap_eq_riemannRochSpace_conorm hex h hF D b))

end FiniteFibres
end TauCeti
end
