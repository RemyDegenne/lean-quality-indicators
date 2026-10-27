public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem isRoot_rB : IsRoot Tag.G2 rB := (isRoot_pos_iff.2 (by simp)).1

end CFSG.Quasithin.H13.Sec53F.G2
end
