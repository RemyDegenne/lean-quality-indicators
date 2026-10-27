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

/-- Natural additive End/vector-group equivalence, independent of basis. -/
@[expose] def endVectorGroupIso :
    vectorGroupFunctor K (Module.End K V) ≅ additiveEndFunctor K V :=
  NatIso.ofComponents (fun R ↦ (endVectorMulEquiv K V R).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      change endVectorLinearEquiv K V S
        (TensorProduct.map (LinearMap.id : Module.End K V →ₗ[K] Module.End K V)
          g.hom.toLinearMap x) =
        endBaseChange K V R S g.hom (endVectorLinearEquiv K V R x)
      exact endVectorLinearEquiv_naturality K V R S g.hom x)

end End
end AlgebraicGeometry
end
end
