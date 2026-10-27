public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

open scoped commutatorElement IsMulCommutative

section QuadZero

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {m : ℕ}

variable {B : LinearMap.BilinForm (ZMod 2) M} {bs : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) M}

theorem quadZero_neg (v : M) : quadZero B bs (-v) = quadZero B bs v := by
  simp [quadZero]

end QuadZero
end CFSG.LocalAnalysis.GorensteinLyons
end
