@[expose] public section

open Function Set

@[inherit_doc]
scoped[AddConstMap] notation:25 G " →+c[" a ", " b "] " H => AddConstMap G H a b

namespace AddConstMapClass

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n := by simp

end AddConstMapClass
end
