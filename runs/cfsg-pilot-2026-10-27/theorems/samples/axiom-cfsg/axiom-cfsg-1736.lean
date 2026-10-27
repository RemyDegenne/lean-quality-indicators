public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Data

variable {Γ : Type} [Group Γ]

theorem centMaxProp_of_data [Finite Γ] {S : Subgroup Γ} {z : Γ} (hS2 : IsPGroup 2 ↥S)
    (hSi : ¬ 2 ∣ S.index) (hz2 : orderOf z = 2) (hcen : centerOf S = Subgroup.zpowers z)
    (hmax : IsMaxSubgroupIn ⊤ (Subgroup.centralizer ({z} : Set Γ))) : CentMaxProp Γ := by
  intro P hP2 hPi W hW hW0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hS2.toSylow hSi) (hP2.toSylow hPi)
  have hPg : P = S.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  have hcenP : centerOf P = (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom := by
    rw [hPg, centerOf_map_equiv (MulAut.conj g), hcen]
  have hcard : Nat.card ↥(centerOf P) = 2 := by
    rw [hcenP, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hz2]
  have hWeq : W = centerOf P := by
    refine Subgroup.eq_of_le_of_card_ge hW ?_
    rw [hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot W).mpr hW0
  rw [hWeq, hcenP, centralizer_map_equiv (MulAut.conj g), centralizer_zpowers_eq]
  exact isMaxSubgroupIn_map (MulAut.conj g) hmax

end Data
end CFSG.Quasithin
end
