public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {L1 L2 S : Subgroup G} {m : ℕ}

theorem Q1_le_centralizer_Z1 (L1 L2 S : Subgroup G) :
    Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  simpa [Z1, omegaOneCenterOf_eq] using
    CFSG.Quasithin.H13.A5.T_le_centralizer_omegaOneCenter (Q1 L1 L2 S)

end CFSG.Quasithin.Stroth
end
