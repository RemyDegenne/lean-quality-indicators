@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

theorem bL_dec_vShort (x : ℕ) :
    QuadraticMap.polarBilin qL (dec x) vShort =
      (popc 24 (x &&& gramRow 12) : ZMod 2) + (popc 24 (x &&& gramRow 13) : ZMod 2) := by
  rw [vShort_eq_ellCls, map_add, bL_dec, bL_dec]
  rfl

end CFSG.Monster.B.Co2
end
