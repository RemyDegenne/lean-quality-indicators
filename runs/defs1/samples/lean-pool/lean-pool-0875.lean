@[expose] public section

open Set Schoenflies

open scoped Graph

namespace Schoenflies

variable {γ : Type*}

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

namespace CellStructure

variable (S : CellStructure γ)

variable {S}

namespace SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

variable {d}

variable (d)

/-- **The abstract subcell relation after an edge subdivision.** Read off the blueprint's
update list, in order: the old pairs that involve neither `e` nor a new cell; the reflexive
pairs of the new cells (see the fidelity note in the module docstring); `v ≼ e₁, e₂`; each old
endpoint below its adjacent new edge; and the new cells below exactly the old *strict*
supercells of `e`. -/
def subRel : γ → γ → Prop := fun σ τ =>
  (σ ∉ d.newCells ∧ τ ∉ d.newCells ∧ σ ≠ d.edge ∧ τ ≠ d.edge ∧ S.sub σ τ) ∨
    (σ = τ ∧ σ ∈ d.newCells) ∨
    (σ = d.newVertex ∧ (τ = d.newEdge₁ ∨ τ = d.newEdge₂)) ∨
    (σ = d.left ∧ τ = d.newEdge₁) ∨
    (σ = d.right ∧ τ = d.newEdge₂) ∨
    (σ ∈ d.newCells ∧ τ ≠ d.edge ∧ S.sub d.edge τ)

end SubdivData
end CellStructure
end Schoenflies
end
