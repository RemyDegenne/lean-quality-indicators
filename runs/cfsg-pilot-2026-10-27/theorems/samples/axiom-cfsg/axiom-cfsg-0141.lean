public section

namespace CFSG.Quasithin.RonanE114

open CFSG.QuasithinUnique CFSG.Quasithin.B6 CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB

open CFSG.Quasithin.A1b

theorem isSolvable_sup_of_normalizes {H : Type} [Group H] [Finite H] {Q T : Subgroup H} (hT : IsPGroup 2 T)
    (hTQ : T ≤ Subgroup.normalizer (Q : Set H)) (hQ : Group.IsSolvable ↥Q) :
    Group.IsSolvable ↥(Q ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : Group.IsSolvable ↥T := by
    have := hT.isNilpotent
    infer_instance
  exact isSolvable_sup_of_le_normalizer_of_isSolvable hTQ hQ hTs

end CFSG.Quasithin.RonanE114
end
