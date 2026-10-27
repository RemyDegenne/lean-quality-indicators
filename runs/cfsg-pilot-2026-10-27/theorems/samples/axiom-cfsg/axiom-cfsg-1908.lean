public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne

namespace ElemAbRankOne

variable {X : Type*} [Group X] {A B : Subgroup X}

theorem map_mulEquiv {Y : Type*} [Group Y] (h : IsElemAbRankOne A B) (e : X ≃* Y) :
    IsElemAbRankOne (A.map e.toMonoidHom) (B.map e.toMonoidHom) :=
  h.map e.surjective (by rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]; exact bot_le)

end ElemAbRankOne
end CFSG.Timmesfeld.ARS
end
