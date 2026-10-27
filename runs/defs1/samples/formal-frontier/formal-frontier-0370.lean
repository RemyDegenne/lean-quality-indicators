set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

/-- Conjugation by `x`, restricted to the right-hand open subgroup.
Its value computes when using stabilizer membership. -/
@[expose]
def mackeyConjugationHom (K : OpenSubgroup G) (x : G) : K →ₜ* G where
  toMonoidHom := (MulAut.conj x).toMonoidHom.comp K.subtype
  continuous_toFun :=
    (IsTopologicalGroup.continuous_conj x).comp continuous_subtype_val

end CorestrictionTransversal
end ContinuousCohomology
end
end
