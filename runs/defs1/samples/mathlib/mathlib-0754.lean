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

namespace GenLoop

section LoopHomeo

variable [DecidableEq N]

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps]
def toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) const where
  toFun t :=
    ⟨(p.val.comp (Cube.insertAt i)).curry t, fun y yH ↦
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl ?_⟩; simp
  target' := by ext t; refine p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr ?_⟩; simp

end LoopHomeo
end GenLoop
end
end
