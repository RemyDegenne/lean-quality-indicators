public section

namespace TauCeti

open AlgebraicGeometry

namespace Divisor

section Extension

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}

variable [Field k] [Field k'] [Field F] [Field F']

variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']

variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

variable (k' F')

section FiniteFibres

variable [hfinite : ∀ P : Place k F, Finite {P' : Place k' F' // P'.restrict k F = P}]

/-- **The conorm on divisor classes** (Stichtenoth, Proposition 3.1.9): the conorm descends to a
homomorphism `Cl(F) →+ Cl(F')` of divisor class groups. -/
noncomputable def conormClassGroup (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') :
    (Place.orderSystem hF).ClassGroup →+ (Place.orderSystem hF').ClassGroup :=
  WeilDivisor.OrderSystem.ClassGroup.lift (Place.orderSystem hF)
    ((Place.orderSystem hF').divisorClass.comp (conorm k' F')) fun z ↦ by
      rw [AddMonoidHom.coe_comp, Function.comp_apply,
        WeilDivisor.OrderSystem.divisorClass_eq_zero_iff]
      exact conorm_mem_principalSubgroup k' F' hF hF'
        ((Place.orderSystem hF).principalDivisor_mem_principalSubgroup z)

end FiniteFibres
end Extension
end Divisor
end TauCeti
end
