@[expose] public section

namespace QuasiBorelSpace

variable
  {A} [QuasiBorelSpace A]
  {B} [QuasiBorelSpace B]
  {C} [QuasiBorelSpace C]

attribute [reducible, instance] Functor.quasiBorelSpace

attribute [reducible, instance] Sequence.quasiBorelSpace

universe u

attribute [local instance] Bundle.quasiBorelSpace

variable {F} [Functor F]

namespace Iter

/-- Successor element constructor. -/
def succ {n} : F (Iter F n) →𝒒 Iter F (n + 1) where
  toFun x := { get := Functor.map getHom x }
  property := by
    apply isHom_comp isHom_mk
    apply QuasiBorelHom.isHom_coe

end Iter
end QuasiBorelSpace
end
