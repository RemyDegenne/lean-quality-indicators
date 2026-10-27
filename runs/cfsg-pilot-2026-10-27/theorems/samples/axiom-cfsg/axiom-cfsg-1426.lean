public section

namespace CFSG.Monster.B.CTIB

open Native

variable {H : Type*} [Group H]

section Xpow

variable {x : H}

theorem xpow_false : xpow x false = 1 := rfl

end Xpow
end CFSG.Monster.B.CTIB
end
