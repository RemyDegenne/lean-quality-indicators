public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Centres

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

theorem i112_pRank_Z_le (hp : p.Prime) (hL : IsComponentOf L ⊤) {r : ℕ}
    (hrel : (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = p) :
    CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ≤ p ^ r := by
  classical
  have : Fintype ↥(i112Orbit B L) := Fintype.ofFinite _
  have hE := i112_isElemAbelian_Z (B := B) hL (Or.inr hZc)
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hE
  rw [pRank_eq_of_card hp.one_lt hE hk]
  have hle := (i112_commFam (B := B) hL).card_centreIn_iSup_le_prod
  rw [i112_iSup_fam] at hle
  have hprod : ∏ i : ↥(i112Orbit B L), Nat.card ↥(centreIn (i112Fam B L i)) = p ^ (p ^ r) := by
    have h1 : ∀ i : ↥(i112Orbit B L), Nat.card ↥(centreIn (i112Fam B L i)) = p := fun i => by
      rw [show i112Fam B L i = (i : Subgroup X) from rfl, i112_card_centreIn_orbit i.2, hZc]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, i112_natCard_orbit, hrel]
  rw [hprod] at hle
  have h2 : p ^ k ≤ p ^ (p ^ r) := hk ▸ hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2

end Centres
end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
end
