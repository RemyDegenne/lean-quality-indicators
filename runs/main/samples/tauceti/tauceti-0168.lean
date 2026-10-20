public section

namespace TauCeti

open CategoryTheory PathAlgebra

universe u v w t

namespace QuiverRep

section Algebra

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q] [DecidableEq Q]

variable (M : QuiverRep.{u, v, w, t} k Q)

@[simp]
theorem toVertex_ofVertex_of_ne {u v : Q} (h : u ≠ v) (z : vertexSpace k Q M v) :
    toVertex k Q M u (ofVertex k Q M v z) = 0 := by
  rw [toVertex_apply, asModuleEquiv_ofVertex, DirectSum.component.of k u v z]
  exact dite_eq_right (Ne.symm h)

end Algebra
end QuiverRep
end TauCeti
end
