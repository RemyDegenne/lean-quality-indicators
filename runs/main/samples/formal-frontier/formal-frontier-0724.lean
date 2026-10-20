@[expose] public section

universe u v w w₁

namespace Subcoalgebra

variable {K : Type u} {C : Type v} {C' : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

variable {C'' : Type w₁} [AddCommGroup C''] [Module K C''] [Coalgebra K C'']

theorem map_le_iff {f : C →ₗc[K] C'} {D : Subcoalgebra K C} {S : Submodule K C'} :
    (map f D).toSubmodule ≤ S ↔ ∀ x ∈ D, f x ∈ S := by
  constructor
  · intro h x hx
    exact h (mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact h x hx

end Subcoalgebra
end
