public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA

attribute [local irreducible] decW u20RecRows u20Gens u20Words u20Basis

open scoped TensorProduct

theorem adjoin_w20End :
    Algebra.adjoin
    (ZMod 2) (Set.range w20End) =
    ⊤ :=
  (congrArg (Algebra.adjoin (ZMod 2)) range_rep20).symm.trans adjoin_rep20

end CFSG.Monster.B.TwoA.Unitary
end
