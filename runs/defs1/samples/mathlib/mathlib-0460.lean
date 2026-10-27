@[expose] public section

open scoped unitInterval Topology

open Homeomorph

noncomputable section

scoped[Topology] notation "I^" N => N → I

variable (N X : Type*) [TopologicalSpace X] (x : X)

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω" => LoopSpace

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω^" => GenLoop

open Topology.Homotopy

variable {N X x}

/-- The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `GenLoop.Homotopic` relation. -/
def HomotopyGroup (N X : Type*) [TopologicalSpace X] (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid N x)

end
end
