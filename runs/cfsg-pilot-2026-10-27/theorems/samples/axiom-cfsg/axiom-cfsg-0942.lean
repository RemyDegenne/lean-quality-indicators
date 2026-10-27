public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

variable (U : Submodule (ZMod 2) (Wv v0))

variable {U}

variable (U)

variable {U}

theorem ker_zuProj :
    (zuProj U).ker = (Ehat ⊓ ZU U).subgroupOf (ZU U) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 : jhatToKv0 ⟨g, ZU_le_Jhat g.2⟩ = 1 := congrArg Subtype.val h
    rw [← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf] at h1
    exact ⟨h1, g.2⟩
  · intro h
    exact Subtype.ext (jhatToKv0_eq_one_of_mem_Ehat _ h.1)

end CFSG.Monster.B.TwoA
end
