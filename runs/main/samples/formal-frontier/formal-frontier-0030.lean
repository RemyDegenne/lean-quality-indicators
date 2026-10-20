@[expose] public section

open CategoryTheory

universe u v w

namespace Action

section Types

variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

@[simp]
theorem autEquivPermCentralizer_apply_symm (α : Aut (ofMulAction G X)) (x : X) :
    (autEquivPermCentralizer G X α : Equiv.Perm X).symm x = α.inv.hom x := rfl

end Types
end Action
end
