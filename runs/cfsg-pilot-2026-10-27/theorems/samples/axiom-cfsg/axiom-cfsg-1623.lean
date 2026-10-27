public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools

open scoped commutatorElement

open CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

open N588

theorem le_M_of_coprime {V : Subgroup G} (hEV : m.E ≤ normalizer (V : Set G))
    (hVp : ¬ m.r ∣ Nat.card V) : V ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI : IsMulCommutative ↥m.E := m.d.E_el.1
  haveI : CFSG.IsElementaryAbelian m.r ↥m.E :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact m.d.E_el.2 x x.2)⟩
  haveI : Nontrivial ↥m.E := (Subgroup.nontrivial_iff_ne_bot _).2 (Mc614.E_ne_bot m.toMc614)
  refine (CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hEV hVp).trans
    (iSup₂_le fun B hB => inf_le_right.trans ?_)
  have hBc : Nat.card B = m.r := by
    have h := B.card_mul_index
    rw [hB, m.d.E_card, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right m.hr.pos h
  have hBp : IsPGroup m.r (B.map m.E.subtype) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Subgroup.card_map_of_injective m.E.subtype_injective, hBc, pow_one]
  have hBne : B.map m.E.subtype ≠ ⊥ := by
    intro h
    have h1 := congrArg (fun H : Subgroup G => Nat.card H) h
    simp only [Subgroup.card_map_of_injective m.E.subtype_injective, hBc,
      Subgroup.card_bot] at h1
    exact m.hr.one_lt.ne' h1
  exact (Subgroup.centralizer_le_normalizer _).trans
    ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 m.r m.E _ (map_subtype_le _)
      (one_le_pRank_of_ne_bot m.hr hBp hBne)).trans m.d.E_gamma)

end Mz614
end CFSG.LocalAnalysis.UniquenessCase.UC6G
end
