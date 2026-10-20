public section

namespace TauCeti

variable (G : Type*) [CommGroup G]

variable {G}

variable {H : Type*} [CommGroup H]

variable {K : Type*} [CommGroup K]

variable (G)

variable {G}

theorem _root_.MonoidHom.twoRank_le_twoRank_add_of_card_ker_le_two_pow
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)] {n : ℕ} (f : G →* H)
    [Finite (MonoidHom.ker f)] (hf : Function.Surjective f)
    (hn : Nat.card (MonoidHom.ker f) ≤ 2 ^ n) :
    twoRank G ≤ twoRank H + n := by
  -- The dimension of the kernel of `G / G² → H / H²` is at most `n`.
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (elementaryTwoQuotientMap f)) ≤ n := by
    have hcard : Nat.card (LinearMap.ker (elementaryTwoQuotientMap f)) ≤ 2 ^ n :=
      (f.card_ker_elementaryTwoQuotientMap_le_card_ker hf).trans hn
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp hcard
  -- Rank-nullity for the induced map, whose range is everything.
  have hrn := LinearMap.finrank_range_add_finrank_ker (elementaryTwoQuotientMap f)
  rw [LinearMap.range_eq_top.mpr (elementaryTwoQuotientMap_surjective f hf), finrank_top] at hrn
  rw [twoRank_def, twoRank_def, ← hrn]
  omega

end TauCeti
end
