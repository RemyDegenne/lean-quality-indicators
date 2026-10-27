public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSmallLie.Child3.SelL39

theorem exists_conj_uCert
    {y : Equiv.Perm (Fin 182)} (hy : y ∈ tT) (hy3 : orderOf y = 3) :
    ∃ c : ↥tT, ∃ i < uCert.pts.size, validA 182 uCert.pts[i]! = true ∧
      permOfArr 182 uCert.pts[i]! = (c : Equiv.Perm (Fin 182))⁻¹ * y * c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have f := u3Facts_of_check Certificates.certificate27266
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec tKeys_lt (enumOK_of_enumOKL f.enum)
  set U := Subgroup.closure (permsA 182 uGens) with hU
  have hUT : U ≤ tT := closure_permsA_le_tT (ws := uWords) (by decide)
  have hUcard : Nat.card (U.subgroupOf tT) = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUT).toEquiv, hcard, f.size]
    norm_num
  have h3 : ¬ 3 ^ (6 + 1) ∣ Nat.card ↥tT := by
    rw [card_tT]
    decide
  have hy' : (⟨y, hy⟩ : ↥tT) ^ 3 = 1 :=
    Subtype.ext (by simpa using (orderOf_eq_iff (by norm_num)).1 hy3 |>.1)
  obtain ⟨c, hc⟩ := exists_conj_mem_of_pow_eq_one hUcard h3 hy'
  rw [Subgroup.mem_subgroupOf] at hc
  have hcy : ((c⁻¹ * ⟨y, hy⟩ * c : ↥tT) : Equiv.Perm (Fin 182)) =
      (c : Equiv.Perm (Fin 182))⁻¹ * y * c := by simp
  rw [hcy] at hc
  obtain ⟨i, hi, hrep⟩ := (hmem _).1 hc
  exact ⟨c, i, hi, hval i hi, hrep⟩

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
end
