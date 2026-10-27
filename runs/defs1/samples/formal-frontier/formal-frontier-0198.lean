public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

/-- The `k`-algebra structure on the global sections of a scheme over `k`.

This is kept as an explicit definition because the structure morphism is data,
not a typeclass parameter of the scheme. -/
@[instance_reducible, expose]
def Hom.globalSectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) : Algebra k Γ(X, ⊤) :=
  (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom).toAlgebra

end Scheme
end AlgebraicGeometry
end
end
