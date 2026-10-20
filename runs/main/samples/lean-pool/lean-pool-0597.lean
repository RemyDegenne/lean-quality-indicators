@[expose] public section

namespace Utilities.Treewidth

open Finset

universe u

variable {V : Type u} {H : SimpleGraph V}

attribute [instance] PartialDecomposition.nodeFintype

attribute [instance] PartialDecomposition.nodeDecidableEq

namespace PartialDecomposition

variable {U : Finset V}

section Join

variable [DecidableEq V] {U₁ U₂ X : Finset V}

@[simp] theorem pairDecomp_bag_inr (H : SimpleGraph V) (X Y : Finset V) (hedge)
    (t : Unit) : (pairDecomp H X Y hedge).bag (Sum.inr t) = Y := rfl

end Join
end PartialDecomposition
end Utilities.Treewidth
end
