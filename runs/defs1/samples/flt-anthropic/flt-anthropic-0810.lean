namespace P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

open scoped Classical NumberField.LevelArith

set_option autoImplicit false

p2m_open

open scoped Classical NumberField.LevelArith

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

namespace P2mS25DecompWD

open scoped TensorProduct Pointwise

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

section Sublattice

variable (p)

variable {V : Type*} [AddCommGroup V] (ρ : Representation ℤ G V)

noncomputable def incl (S T : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (hT : ∀ g, ∀ v ∈ T, ρ g v ∈ T)
    (hST : S ≤ T) : X p (subRep ρ S hS) →ₗ[MonoidAlgebra (ZMod p) G] X p (subRep ρ T hT) :=
  redHom p _ _ (Submodule.inclusion hST) (fun g v => rfl)

end Sublattice
end P2mS25DecompWD
end P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add
