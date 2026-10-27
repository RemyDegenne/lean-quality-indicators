public section

namespace CFSG.Monster.Code

open F4

theorem mem_H_iff (x : Fin 24 → ZMod 2) : x ∈ H ↔ ∃ y ∈ H₆, l y = x := Iff.rfl

end CFSG.Monster.Code
end
