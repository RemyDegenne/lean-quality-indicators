@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]

section ModObj

open MonObj AddMonObj

open scoped MonoidalLeftAction

variable (M : C) [MonObj M]

variable {M}

namespace ModObj

attribute [local instance] regular in
@[to_additive (attr := simp)]
lemma smul_eq_mul (M : C) [MonObj M] : γ[M,M] = μ[M] := rfl

end ModObj
end ModObj
end CategoryTheory
end
