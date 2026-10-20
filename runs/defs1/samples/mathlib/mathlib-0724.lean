@[expose] public section

section

open Function

variable (F A B C D E : Type*)

variable [Monoid A] [Monoid B] [Monoid C] [Monoid D]

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

namespace ContinuousMonoidHom

infixr:25 " →ₜ+ " => ContinuousAddMonoidHom

infixr:25 " →ₜ* " => ContinuousMonoidHom

variable {A B C D E}

variable (A B C D E)

/-- For `f : F` where `F` is a class of continuous monoid hom, this yields an element
`ContinuousMonoidHom A B`. -/
@[to_additive /-- For `f : F` where `F` is a class of continuous additive monoid hom, this yields
an element `ContinuousAddMonoidHom A B`. -/]
def ofClass (F : Type*) [FunLike F A B] [ContinuousMapClass F A B]
    [MonoidHomClass F A B] (f : F) : (ContinuousMonoidHom A B) := toContinuousMonoidHom f

end ContinuousMonoidHom
end
end
