public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem t1bLieHardAt_E6_of_rank (hU : E6RankUpper) (hL : E6RankLower) : T1bLieHardAt .E6 := by
  intro L _ _ hLC hq hK p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  simp only [OutEasy, not_or, not_not, ne_eq] at hE
  obtain ⟨rfl, h1, h2⟩ := hE
  have hpar : IsE6Params .E6 r f := Or.inl ⟨rfl, h1⟩
  have h9 : 9 ∣ r ^ f - 1 := nine_dvd_of_three_dvd_exponent h2 h1
  obtain ⟨hS6, hA7⟩ := hU _ .E6 n r f hm hpar
  obtain ⟨hZ, hlow⟩ := hL L hq .E6 n r f hm hpar
  have hmono := pRank_mulAut_le_mulAut_centerQuotient hq.1 hp
  by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center L)
  · have := hZ hZ3
    omega
  · have h6 := hlow (fun _ => h9) (fun h => by cases h)
    have := pRank_centerQuotient_le_of_not_dvd hp hZ3
    omega

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
end
