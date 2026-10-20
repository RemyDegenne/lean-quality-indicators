public section

namespace TauCeti.QuiverRep

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

variable (M N : QuiverRep.{u, v, w, t} k Q)

/-- The vertex components of a morphism of representations, retyped between vertex spaces. -/
noncomputable def homVertex (f : M ⟶ N) : HomVertex M N :=
  fun i ↦ (f.app ((Paths.of Q).obj i)).hom

end TauCeti.QuiverRep
end
