public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_p_eq_three (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) : p = 3 := by
  obtain ⟨n, hn1, hn2⟩ := hc.core.card_nineOmegaIn
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  have hfr := nine3_oddFrame hc hI hρ
  rcases h35 with h3 | h5
  · have hpow : 2 ^ n = 2 := by omega
    rw [hn1, hpow] at hfr
    exact nine3OddFrame_two_p hc.core.hyp.base.prime hc.core.hyp.base.odd hfr
  · have hpow : 2 ^ n = 4 := by omega
    have h3' : 3 ≤ Nat.card ↥(nineDelta V S) := by omega
    have hi := nine3_fibreIndep hc hI h3' hρ
    rw [hn1, hpow] at hfr
    exact nine3OddFrame_four_p hc.core.hyp.base.prime hc.core.hyp.base.odd hfr hi

end CFSG.LocalAnalysis.WeakClosure81
end
