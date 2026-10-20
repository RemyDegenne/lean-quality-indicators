@[expose] public section

open Set Topology Filter

variable {X Y Z : Type*}

@[inherit_doc]
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.isQuotientMap.isCoinducing.eq_coinduced.symm

end Homeomorph
end
