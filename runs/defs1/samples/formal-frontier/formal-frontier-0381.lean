public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

section End

variable (V : Type u) [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

/-- The finite-dimensional additive End functor is represented by the existing
basis-independent vector-group scheme and its finite-type coordinate ring,
refining the chosen-basis matrix comparison of Milne, *Algebraic Groups*
(2017), item 2.7, without choosing a basis. -/
@[expose] def endGroupPointsIso :
    additiveEndFunctor K V ≅ vectorGroupPointsFunctor K (Module.End K V) :=
  (endVectorGroupIso K V).symm ≪≫ vectorGroupPointsIso K (Module.End K V)

end End
end AlgebraicGeometry
end
end
