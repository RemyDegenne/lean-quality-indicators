public section

namespace CFSG.Wreathed.OddFieldTorus

open Matrix

section Fixed

variable {F : Type*} [Field F]

theorem card_fixedField_eq (σ : F ≃+* F) :
    Nat.card (fixedField σ) = Nat.card {a : F // σ a = a} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixedField)

end Fixed
end CFSG.Wreathed.OddFieldTorus
end
