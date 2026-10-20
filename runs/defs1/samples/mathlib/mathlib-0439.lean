@[expose] public section

universe u v

open CategoryTheory

attribute [instance] AddMonCat.str MonCat.str

attribute [instance] AddCommMonCat.str CommMonCat.str

namespace CommMonCat

/-- The forgetful functor from `CommMonCat` to `MonCat` is fully faithful. -/
@[to_additive fullyFaithfulForgetToAddMonCat
  /-- The forgetful functor from `AddCommMonCat` to `AddMonCat` is fully faithful. -/]
def fullyFaithfulForgetToMonCat : (forget₂ CommMonCat.{u} MonCat.{u}).FullyFaithful where
  preimage f := ofHom f.hom

end CommMonCat
end
