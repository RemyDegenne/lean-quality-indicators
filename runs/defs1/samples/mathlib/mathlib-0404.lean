@[expose] public section

namespace ZMod

section QuadCharModP

/-- Define the second primitive quadratic character on `ZMod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
@[simps]
def χ₈' : MulChar (ZMod 8) ℤ where
  toFun a :=
    match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 3 => 1
    | 5 | 7 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

end QuadCharModP
end ZMod
end
