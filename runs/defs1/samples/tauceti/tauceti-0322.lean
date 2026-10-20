public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

universe u v w x

variable (R : Type u) [CommSemiring R]

variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable (A : Type x) [Semiring A] [Algebra R A]

namespace FGComoduleCat

/-- Scalar extension of the underlying-module functor on finitely generated comodules. -/
noncomputable def scalarExtensionFunctor :
    FGComoduleCat.{u, v, w} R C ⥤ SemimoduleCat.{max x w} A :=
  incl ⋙ ComoduleCat.scalarExtensionFunctor R C A

end FGComoduleCat
end TauCeti
end
