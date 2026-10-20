@[expose] public section

attribute [local implicit_reducible]
  Quiver.Symmetrify IsFreeGroupoid.Generators
  WideSubquiver WideSubquiver.toType WideSubquiver.quiver IsFreeGroupoid.quiverGenerators
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify

open Set Function

open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace FiniteGraphFreeGroup

variable {V : Type u} [Quiver.{u} V]

/-- The penultimate vertex, prefix path, and last edge of the rooted path to a non-root vertex. -/
noncomputable def lastData (T : WideSubquiver V) [Arborescence T]
    (b : {b : T // b ≠ root T}) :
    Σ a : T, Path (root T) a × (a ⟶ b.1) :=
  Classical.choice (exists_last_data T (b := b.1) b.2)

end FiniteGraphFreeGroup
end
end
