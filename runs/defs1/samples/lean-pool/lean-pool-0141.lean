@[expose] public section

attribute [local implicit_reducible] Computableℝ ComputableℝSeq.nzSeq

namespace Computableℝ

variable (x y : Computableℝ)

section ordered

variable (x y : Computableℝ)

/-- Definition of `lt`. -/
def lt : Prop := by
  apply Quotient.lift (fun z ↦ z.sign = SignType.pos) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]

end ordered
end Computableℝ
end
