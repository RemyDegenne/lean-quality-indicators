@[expose] public section

universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

namespace EquivFunctor

section

variable (f : Type u₀ → Type u₁) [EquivFunctor f] {α β : Type u₀} (e : α ≃ β)

/-- An `EquivFunctor` in fact takes every equiv to an equiv. -/
def mapEquiv : f α ≃ f β where
  toFun := EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert! (congr_fun (EquivFunctor.map_trans' e e.symm) x).symm
    simp
  right_inv y := by
    convert! (congr_fun (EquivFunctor.map_trans' e.symm e) y).symm
    simp

end
end EquivFunctor
end
