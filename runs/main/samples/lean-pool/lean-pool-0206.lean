@[expose] public section

namespace BeyondBethe

open Complexity

@[simp] theorem machineFullAdderCarry_one (a b carry : Bool) :
    machineFullAdderCarry [a] [b] [carry] =
      [(a && b) || (a && carry) || (b && carry)] := by
  cases a <;> cases b <;> cases carry <;> rfl

end BeyondBethe
end
