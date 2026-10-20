@[expose] public section

open Function

open scoped Finset

universe u v

variable {η α ι κ : Type*}

namespace Combinatorics

namespace Subspace

variable {η α ι κ : Type*} {l : Subspace η α ι} {x : η → α} {i : ι} {a : α} {e : η}

variable {η' α' ι' : Type*}

protected lemma IsMono.reindex {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι → α) → κ}
    (hl : l.IsMono C) : (l.reindex eη eα eι).IsMono fun x ↦ C <| eα.symm ∘ x ∘ eι := by
  simp [reindex_isMono, Function.comp_assoc]; simpa [← Function.comp_assoc]

end Subspace
end Combinatorics
end
