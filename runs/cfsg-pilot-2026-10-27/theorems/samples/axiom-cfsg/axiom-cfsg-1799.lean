public section

namespace CFSG.ASVolI

open CFSG.Open

section MP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [CharP K 2]

open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

theorem burnsideB46_mp_ncard_stdF [Finite K] {h : ℕ} (hh : h ≤ 6) :
    ((stdF K h : Submodule K (Ix3 → K)) : Set (Ix3 → K)).ncard = Nat.card K ^ h := by
  rw [← Nat.card_coe_set_eq]
  exact card_stdF hh

end MP
end CFSG.ASVolI
end
