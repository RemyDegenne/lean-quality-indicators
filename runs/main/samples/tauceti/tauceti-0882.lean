public section

open scoped unitInterval Topology Topology.Homotopy

open Topology.Homotopy

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)] {z : ∀ i, Z i}

@[simp]
theorem piEquiv_symm_apply (z : ∀ i, Z i) (a : ∀ i, HomotopyGroup N (Z i) (z i)) :
    (piEquiv z).symm a = pi a :=
  (rfl)

end HomotopyGroup
end
