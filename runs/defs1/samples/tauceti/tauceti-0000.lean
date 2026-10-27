public section

namespace TauCeti.DynkinType

open TauCeti.F4ShortRoot

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module

open scoped TensorProduct

noncomputable section

/-- The canonical quotient-column polynomial after transport to the short-root ideal. -/
noncomputable def f4ShortRootTransportedQuotientPolynomial
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    A ⊗[ZMod 2] f4ShortRootLieIdeal :=
    (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a + t • ((1 : A) ⊗ₜ[ZMod 2]
        f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a)) +
      t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientToIdealEquiv
          (f4ShortRootQuotientDividedSquareColumn k a))

end
end TauCeti.DynkinType
end
