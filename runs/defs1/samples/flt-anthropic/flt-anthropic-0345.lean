namespace P2MW.S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic

open ZMod NumberTheorySymbols

namespace HilbertRecipPort

def Iso {F : Type*} [Field F] (A B : F) : Prop :=
  ∃ z x y : F, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - A * x ^ 2 - B * y ^ 2 = 0

end HilbertRecipPort
end P2MW.S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic
