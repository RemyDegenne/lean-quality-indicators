@[expose] public section

universe u v

open Finset

attribute [instance_reducible, instance 100] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α → Type v}

open Function

/-- A type with unique inhabitant has a trivial enumeration. Not registered as an instance, to make
sure that there aren't two definitionally differing instances around. -/
@[instance_reducible]
def ofUnique [Unique α] : FinEnum α := default

end FinEnum
end
