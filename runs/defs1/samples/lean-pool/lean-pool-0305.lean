@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

section ModMultiDefs

variable {A} in
/-- The relation object of a slot, in slot form. -/
abbrev ModSlot.mid [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    {Xs : List (Mod D A)} (s : ModSlot Xs) : D :=
  modMultiMid A s.pre s.fst s.snd s.post

end ModMultiDefs
end RS
end
