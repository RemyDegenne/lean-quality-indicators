public section

open IsDedekindDomain

open scoped WithZero

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}

variable [Field k] [Field F] [Algebra k F]

variable [Field k'] [Field F']

variable [Algebra k k'] [Algebra k' F'] [Algebra F F'] [Algebra k F']

variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section ResidueField

variable (k F) (P' : Place k' F') [Algebra.IsIntegral F F']

/-- The **relative degree** `f(P' ∣ P) = [F'_{P'} : F_P]` of a place `P'` of `F' / k'` over the
place `P` of `F / k` it lies over (Stichtenoth, Definition 3.1.5). -/
noncomputable def relativeDegree : ℕ :=
  Module.finrank (P'.restrict k F).ResidueField P'.ResidueField

end ResidueField
end Place
end TauCeti
end
