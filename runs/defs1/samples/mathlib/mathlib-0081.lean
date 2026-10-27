@[expose] public section

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

notation3 "Π₀ "(...)", "r:(scoped f => DFinsupp f) => r

namespace DFinsupp

section DecidableEq

variable [DecidableEq ι]

section SupportBasic

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `Finset`. -/
def support (f : Π₀ i, β i) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i ≠ 0) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩

end SupportBasic
end DecidableEq
end DFinsupp
end
