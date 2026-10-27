public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Vertex

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem sup_left_le_p1 (L1 L2 S : Subgroup G) : L1 ⊔ S ≤ P1 L1 L2 S :=
  sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)

end Vertex
end CFSG.Quasithin.Stroth
end
