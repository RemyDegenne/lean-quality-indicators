@[expose] public section

variable {α β : Type*}

open Nat

section CommMonoid

variable [CommMonoid α]

theorem emultiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : emultiplicity a u = 0 :=
  emultiplicity_of_isUnit_right ha u.isUnit

end CommMonoid
end
