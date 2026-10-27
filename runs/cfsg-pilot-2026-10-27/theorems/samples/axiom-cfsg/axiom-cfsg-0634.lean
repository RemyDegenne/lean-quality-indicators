public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup

variable {W : Type*} [Group W]

theorem mem_normSub (hc : ∀ x y : W, x * y = y * x) {α : MulAut W} {w : W} :
    w ∈ normSub hc α ↔ norm5 hc α w = 1 := MonoidHom.mem_ker

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
end
