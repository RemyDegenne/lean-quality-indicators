@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section GroupInstances

variable [Mul F]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a right cancel semigroup if `β` is a
right cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a right cancel additive
semigroup if `β` is a right cancel additive semigroup. -/]
protected abbrev rightCancelSemigroup [RightCancelSemigroup β] [IsMulApply F] :
    RightCancelSemigroup F :=
  DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

end GroupInstances
end FunLike
end
