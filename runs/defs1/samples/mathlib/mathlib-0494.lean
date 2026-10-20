public section

universe u

namespace EckmannHilton

variable {X : Type u}

local notation a " <" m:51 "> " b => m a b

/-- `IsUnital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
structure IsUnital (m : X → X → X) (e : X) : Prop extends Std.LawfulIdentity m e

end EckmannHilton
end
