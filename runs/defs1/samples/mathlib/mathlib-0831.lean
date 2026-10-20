@[expose] public section

namespace Stream'

universe u v w

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

section MLList

/-- Embed a `MLList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `MLList`s created by meta constructions. -/
def ofMLList : MLList Id α → Seq α :=
  corec fun l =>
    match l.uncons with
    | .none => none
    | .some (a, l') => some (a, l')

end MLList
end Seq
end Stream'
end
