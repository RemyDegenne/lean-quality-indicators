public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG.Assembly (IsElemAbelian)

theorem isElemAbelian_subgroupOf {W : Type*} [Group W] {p : ℕ} {E : Subgroup W} (J : Subgroup W)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf J) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE J

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
end
