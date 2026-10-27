public section

namespace CFSG.Quasithin.H13.U3.P2

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

theorem card_eq_two_pow_of_le {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQP : Q ≤ P) :
    ∃ n, Nat.card Q = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hP.to_le hQP).exists_card_eq

end CFSG.Quasithin.H13.U3.P2
end
