public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

theorem comm15_eq (s w : E) : ⁅c.x1 s, c.x5 w⁆ = c.y (c.F2 s w) (c.F3 s w) (c.F4 s w) :=
  Classical.choose_spec (c.exists_comm15_eq s w)

end Coords
end CaseH
end CFSG.Timmesfeld.ARS
end
