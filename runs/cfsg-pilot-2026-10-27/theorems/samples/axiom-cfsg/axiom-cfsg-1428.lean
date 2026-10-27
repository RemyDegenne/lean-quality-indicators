public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Polynomial Matrix

theorem classSet_nonempty {i : ℕ} (hi : i < 12) : (e8F5ClassSet i).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by rw [ncard_classSet hi]; norm_num)

end CFSG.RankThree.Lattice
end
