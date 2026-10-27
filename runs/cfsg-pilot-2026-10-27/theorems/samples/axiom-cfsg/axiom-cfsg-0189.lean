public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section

theorem quatEquiv_pw_cast {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (k : ℤ) : quatEquiv_pw a (k : ZMod N) = a ^ k :=
  quatEquiv_zpow_val ha k

end
end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
end
