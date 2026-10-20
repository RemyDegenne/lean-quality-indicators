@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section

variable (C : Type u₁) [CategoryStruct.{v₁} C] (D : Type u₂) [CategoryStruct.{v₂} D]

variable {C D}

open CategoryTheory.Prod

@[simp]
theorem eqToHom_snd {X Y : C × D} (h : X = Y) :
    (eqToHom h).2 = eqToHom (h ▸ rfl) := by subst h; rfl

end
end CategoryTheory
end
