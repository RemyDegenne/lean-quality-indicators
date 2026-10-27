public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Bad

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup MulAction

section Setting

variable {G : Type} [Group G] [Finite G] {z : G} {Z A : Subgroup G} {T : Sylow 2 G} {k : G}

theorem odd_relIndex (c : BL.Ctx z 2 Z A T) : Odd ((T : Subgroup G).relIndex (Hz z)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := relIndex_mul_index c.hTH
  have h2 : ¬ 2 ∣ (T : Subgroup G).index := T.not_dvd_index
  have h3 : ¬ 2 ∣ (T : Subgroup G).relIndex (Hz z) := fun h => h2 (h1 ▸ Dvd.dvd.mul_right h _)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

end Setting
end CFSG.GF2Type.Aschbacher1976Full.HS.Bad
end
