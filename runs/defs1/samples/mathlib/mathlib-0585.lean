@[expose] public section

open Module Polynomial

namespace IntermediateField

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : Finset E` such that
`IntermediateField.adjoin F t = S`.

We use the class `Algebra.EssFiniteType F E` instead of `(⊤ : IntermediateField F E).FG` to say that
`E` is finitely generated as an `F` extension.
See `IntermediateField.fg_top_iff`. -/
@[stacks 09FZ "second part"]
def FG (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F ↑t = S

end Induction
end IntermediateField
end
