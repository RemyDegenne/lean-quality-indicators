@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

variable {C : Type u₁} [Category.{v₁} C]

variable (J : GrothendieckTopology C)

variable (A : Type u₂) [Category.{v₂} A]

variable {J} {A}

variable (J) in
/-- A terminal object in `A` gives rise to a terminal object in `Sheaf J` -/
@[simps]
def Sheaf.terminal {X : A} (hX : IsTerminal X) : Sheaf J A where
  obj := (CategoryTheory.Functor.const _).obj X
  property := Presheaf.isSheaf_of_isTerminal J hX

end CategoryTheory
end
end
