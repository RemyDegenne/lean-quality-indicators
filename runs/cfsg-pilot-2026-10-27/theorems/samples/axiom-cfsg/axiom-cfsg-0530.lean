public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

open scoped commutatorElement

section Clauses

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

theorem hc5_U_eq
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {a b : vStab cv0}
    (hZPeq : hc5ZP u X = Subgroup.closure {a, b}) :
    X ⊓ Subgroup.centralizer X ⊓ ⁅X, X⁆ = Subgroup.closure {a, b} := by
  rw [inf_centralizer_eq_map_center, center_inf_commutator_eq hvu hβ hXβ hX, hZPeq]

end Clauses
end CFSG.Monster.B.GSide
end
