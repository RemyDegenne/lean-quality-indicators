@[expose] public section

open Function

open scoped Pointwise

universe u v w x

namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

local notation " Q " => G ⧸ N

variable (φ : G →* H)

open MonoidHom

section ZPow

variable {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]

variable (f : A →* B) (g : B →* A) (e : A ≃* B) (d : B ≃* C) (n : ℤ)

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_comp :
    homQuotientZPowOfHom (f.comp g) n =
      (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) :=
  monoidHom_ext _ rfl

end ZPow
end QuotientGroup
end
