@[expose] public section

universe uι uR uS uM uN

namespace KTheory

namespace K0

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

theorem fst_comp_prodEquiv :
    (AddMonoidHom.fst (K0 R) (K0 S)).comp
        (prodEquiv R S).toAddMonoidHom = map (RingHom.fst R S) := by
  rfl

end Prod
end K0
end KTheory
end
