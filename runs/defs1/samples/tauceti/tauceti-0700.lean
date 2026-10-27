public section

open CategoryTheory HomologicalComplex MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

section Blocks

variable (R : Type*) [CommSemiring R]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The projection onto the off-center block. -/
noncomputable def stabilizeXOffCenterProjection :
    GridChainMinus R (n + 1) →ₗ[S] (G.StabilizeXOffCenterState s →₀ S) :=
  Finsupp.lcomapDomain _ Subtype.val_injective

end Blocks
end GridDiagram
end TauCeti
end
