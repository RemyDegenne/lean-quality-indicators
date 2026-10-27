@[expose] public section

universe v v' u u'

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type u} {D : Type u'}

section

variable [CategoryStruct.{v} C] [CategoryStruct.{v'} D]

/-- The typeclass associated to `P : ObjectProperty C`. -/
@[mk_iff]
class Is (P : ObjectProperty C) (X : C) : Prop where
  prop : P X

end
end ObjectProperty
end CategoryTheory
end
