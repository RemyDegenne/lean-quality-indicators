public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem commutator_DA :
    commutator DA = ⊤ := by
  have : IsSimpleGroup DA := isSimpleGroup_DA
  have hn : (commutator DA).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    have hc := (commutator_eq_bot_iff_center_eq_top DA).1 h
    apply tauhatA_not_commute_xhatA
    have hx : xhatA ∈ Subgroup.center DA := hc ▸ Subgroup.mem_top _
    exact Subgroup.mem_center_iff.1 hx tauhatA
  · exact h

end CFSG.Monster.Existence
end
