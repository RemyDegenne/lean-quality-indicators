public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1117StepsProof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem conj_x_e_mem (h : Sec11Data G A c L a R Y d x s r g) {e : G} (he : e ∈ A) :
    x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨z, hz, hxz⟩ := Item1117Proof.exists_conj_of_mem_A h he
  have hzA : z ∈ A := Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_A h) hz
  rw [hxz, Item1117Proof.commute_of_mem_A h he hzA, mul_inv_cancel_right]
  exact hz

end Data
end Item1117StepsProof
end CFSG.RankThree.PartTwo.Sec11
end
