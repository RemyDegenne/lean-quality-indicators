@[expose] public section

open Finset

namespace UniqueMul

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

section Opposites

open Finset MulOpposite

@[to_additive]
theorem iff_mulOpposite :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) ↔
      UniqueMul A B a0 b0 :=
  ⟨of_mulOpposite, to_mulOpposite⟩

end Opposites
end UniqueMul
end
