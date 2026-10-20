@[expose] public section

section Type'

variable (F G : Type*) {α γ : Type*} {β : α → Type*} [DFunLike F α β] [FunLike G α γ]

/-- All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.fintype` that might be easier to infer.
This is not an instance because specific `FunLike` types might have a better-suited definition.
-/
@[instance_reducible]
noncomputable def FunLike.fintype [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G :=
  DFunLike.fintype G

end Type'
end
