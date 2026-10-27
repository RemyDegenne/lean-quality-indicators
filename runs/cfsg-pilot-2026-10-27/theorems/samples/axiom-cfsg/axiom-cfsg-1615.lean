public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)} {K : Subgroup G}

theorem fsuU_le_pCoreOf (C : Ctx14332 G T L V V₂ g a D) : fsuU T V ≤ pCoreOf 2 (l32nH T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 C.U_le
    (l32nH_le_normalizer_fsuU T V) C.U2

end L14332
end CFSG.Quasithin.H13
end
