@[expose] public section

variable {F α β R S S' : Type*}

infixl:25 " ≃+* " => RingEquiv

namespace RingEquivClass

variable [EquivLike F R S]

attribute [instance 100] toAddEquivClass

/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
@[coe]
def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F) :
    α ≃+* β :=
  { (f : α ≃* β), (f : α ≃+ β) with }

end RingEquivClass
end
