public section

set_option warningAsError true

noncomputable section

open Set

open scoped RestrictedProduct

namespace RestrictedProduct

open Multiplicative

/-- The standard symmetric bicharacter on a finite cyclic group, in multiplicative notation. -/
@[expose] def zmodBicharacter (n : ℕ) [NeZero n] :
    Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Circle :=
  AddChar.toMonoidHomMulEquiv.toMonoidHom.comp
    (AddChar.toMonoidHom (AddChar.zmodHom (n := n)) :
      Multiplicative (ZMod n) →* AddChar (ZMod n) Circle)

end RestrictedProduct
end
end
