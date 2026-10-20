@[expose] public section

namespace PDL

/-- Membership of a negated ordinary or loaded formula in a sequent. -/
def AnyNegFormula.memSequent : (X : Sequent) → (anf : AnyNegFormula) → Prop
| X, ⟨.normal φ⟩ => (~φ) ∈ X
| X, ⟨.loaded χ⟩ => instMembershipNegLoadFormulaSequent.mem X (~'χ)

end PDL
end
