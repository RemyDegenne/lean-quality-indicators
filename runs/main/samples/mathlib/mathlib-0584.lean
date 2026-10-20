@[expose] public section

open Set

variable {α : Type*}

namespace RelIso

variable {r : α → α → Prop} {x : α} [IsTrans α r] [Std.Trichotomous r] [DecidableRel r]

@[simp]
theorem sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

end RelIso
end
