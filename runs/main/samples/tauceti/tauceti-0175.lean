public section

open CategoryTheory

open scoped Pointwise

universe u v w

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G]

theorem conjRepFunctor_map_hom_toLinearMap [Semiring k] (s : G) {H : Subgroup G}
    {A B : Rep k H} (f : A ⟶ B) :
    ((conjRepFunctor s H).map f).hom.toLinearMap = f.hom.toLinearMap :=
  rfl

end TauCeti
end
