@[expose] public section

open CategoryTheory Limits WalkingParallelPair

universe v u

variable (R : Type u) [Semiring R]

attribute [instance] SemimoduleCat.isAddCommMonoid SemimoduleCat.isModule

namespace SemimoduleCat

section

variable {R}

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : SemimoduleCat.{v} R) (f : Hom A B) :=
  f.hom

end
end SemimoduleCat
end
