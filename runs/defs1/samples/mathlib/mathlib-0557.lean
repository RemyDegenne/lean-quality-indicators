@[expose] public section

open Function (iterate_succ iterate_succ_apply iterate_zero_apply)

namespace Turing

section ListBlank

/-- Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def BlankExtends.above {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
    (h₂ : BlankExtends l l₂) : { l' // BlankExtends l₁ l' ∧ BlankExtends l₂ l' } :=
  if h : l₁.length ≤ l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩

end ListBlank
end Turing
end
