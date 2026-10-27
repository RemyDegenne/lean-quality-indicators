public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

open CFSG.Assembly

open CFSG.RankThree.Classical2 (orthDerived)

open OrthTorus

theorem ggOrthSignedTorusInput_holds : GGOrthSignedTorusInput := by
  refine ⟨fun K _ _ _ m p hm hmo hp hpq => ?_, fun K _ _ _ m p b c hm hirr hp hpq => ?_⟩
  · have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    refine ggTorusSignedEltSC_of_mulEquiv (rPlusEquiv K (by omega))
      (torusSignedEltSC_orthDerived hp hp2 (Or.inr hpq) (TableBOrth.nondegenerate_qPlusForm _)
        (exists_totallySingular_qPlusForm (by omega)) ?_)
    rw [charSum_qPlusForm]
    intro h
    have h1 := (modEq_neg_one_of_dvd hpq).pow (n + 1)
    rw [Odd.neg_one_pow hmo] at h1
    exact neg_one_not_modEq_one hp hp2 (h1.symm.trans h)
  · have hp2 : p ≠ 2 := by
      rcases hpq with h | ⟨-, h⟩
      · exact ne_two_of_dvd_card_sub_one h
      · exact SpNS.ne_two_of_dvd_card_add_one h
    obtain ⟨hS, hT⟩ := charSum_qMinusForm m hirr
    refine ggTorusSignedEltSC_of_mulEquiv (rMinusEquiv K m b c)
      (torusSignedEltSC_orthDerived hp hp2 (hpq.imp id fun h => h.2)
        (TableBOrth.nondegenerate_qMinusForm m hirr) (hT hm) ?_)
    rw [hS]
    intro h
    have hq : (Nat.card K : ℤ) ^ (m + 1) ≡ 1 [ZMOD p] := by
      rcases hpq with h1 | ⟨hmo, h1⟩
      · simpa using (modEq_one_of_dvd Nat.card_pos h1).pow (m + 1)
      · have h2 := (modEq_neg_one_of_dvd h1).pow (m + 1)
        rwa [Even.neg_one_pow hmo.add_one] at h2
    exact neg_one_not_modEq_one hp hp2 (hq.neg.symm.trans h)

end CFSG.StandardType
end
