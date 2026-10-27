public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} {c : Ctx S}

theorem IsW.factorization_three_card
    {W : Subgroup G} (hW : c.IsW W) : (Nat.card G).factorization 3 = 6 := by
  have h := hW.card_eq_sylow
  rw [hW.card] at h
  exact (Nat.pow_right_injective (a := 3) (by norm_num) h).symm

end Ctx
end Setup
end CFSG.Sporadic.Recognition.JankoWong
end
