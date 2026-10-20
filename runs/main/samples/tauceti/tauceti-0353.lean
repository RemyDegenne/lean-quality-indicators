public section

namespace TauCeti

open Pointwise Topology

variable {E X A : Type*} {G : Type*} [Group G] [MulAction G E] [MulAction G A] {q : E → X}

namespace BalancedProduct

@[simp]
theorem equivSelf_symm_apply (e : E) :
    (equivSelf (G := G) (E := E)).symm e = mk G e 1 :=
  (rfl)

end BalancedProduct
end TauCeti
end
