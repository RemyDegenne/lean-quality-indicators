public section

open CategoryTheory Limits Opposite Topology

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

local instance globalSectionsAlgebraInstance
    (X : Over (Spec (.of K))) : Algebra K Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra K

/-- The canonical map from a scheme to its finite-etale component scheme,
as in J. S. Milne, *Algebraic Groups* (2017), in the paragraph immediately
before Proposition 1.30. -/
@[expose]
def toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : X ⟶ componentScheme X :=
  toSpecOver X (componentSubalgebra X).val

end
end AlgebraicGeometry
end
