@[expose] public section

open Function Multiplicative

open Finset hiding card

open Fintype (card)

namespace AddChar

section fromAddCommGrouptoDivisionCommMonoid

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

@[simp] lemma zpow_apply (ψ : AddChar A M) (n : ℤ) (a : A) : (ψ ^ n) a = ψ a ^ n := zsmul_apply ..

end fromAddCommGrouptoDivisionCommMonoid
end AddChar
end
