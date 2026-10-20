@[expose] public section

open Function Set

@[inherit_doc]
scoped[AddConstMap] notation:25 G " →+c[" a ", " b "] " H => AddConstMap G H a b

open AddConstMapClass

namespace AddConstMap

section FloorRing

variable {R G : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [AddGroup G]
  (a : G)

/-- A map `f : R →+c[1, a] G` is defined by its values on `Set.Ico 0 1`. -/
def mkFract : (Ico (0 : R) 1 → G) ≃ (R →+c[1, a] G) where
  toFun f := ⟨fun x ↦ f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x ↦ by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

end FloorRing
end AddConstMap
end
