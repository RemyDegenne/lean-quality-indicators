@[expose] public section

universe u v

open CategoryTheory Limits

variable (V : Type*) [Category* V]

namespace Action

variable {V}

variable (G : Type*) [Monoid G]

variable {G}

section Forget

variable (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `CategoryTheory.forget` API provided by the `ConcreteCategory` instance below,
rather than using this directly.
-/
@[implicit_reducible, simps]
def forget : Action V G ⥤ V where
  obj M := M.V
  map f := f.hom

end Forget
end Action
end
