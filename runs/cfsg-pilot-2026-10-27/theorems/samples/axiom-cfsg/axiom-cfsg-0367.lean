public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

open scoped commutatorElement

namespace S512N

section Embed

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem coe_eM (m : ↥M) : (eM hTM m : (puAmalgam hTM).Universal) = (puAmalgam hTM).ofA m := rfl

end Embed
end S512N
end CFSG.Quasithin.MS93
end
