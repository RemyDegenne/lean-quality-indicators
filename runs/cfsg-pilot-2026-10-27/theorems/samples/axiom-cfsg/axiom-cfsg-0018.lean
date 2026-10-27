public section

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Blueprint CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.InvFam
  CFSG.KC.CoTwoAut CFSG.KC.Co1M CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.Module.CoTwo

open CFSG.Monster.GMS (co1Orbit co1Stab)

attribute [local instance] Odd.vecAct Odd.vecSMul

theorem orbit_eq_orbitSet (H : Subgroup NativeSporadic.Co1) (x : Vec24) :
    MulAction.orbit H x = orbitSet co1Act H x := by
  ext y
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

end CFSG.Sporadic.Co1.Module.CoTwoAut
end
