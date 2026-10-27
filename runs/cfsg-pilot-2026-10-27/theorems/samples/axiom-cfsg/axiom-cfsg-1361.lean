public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace TableB

section Rank

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map {H : Type*} [Group H] {p : ℕ} {E : Subgroup H}
    (hE : IsElemAbelian p E) (f : H →* G) : IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

end Rank
end TableB
end CFSG.StandardType
end
