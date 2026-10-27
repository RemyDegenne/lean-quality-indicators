@[expose] public section

universe u v w

variable {G : Type u} {X : Type v}

open Function

open scoped commutatorElement

namespace MulAction

variable [Group G]

open QuotientGroup

variable (G)

variable [MulAction G X] (x : X)

variable (X)

local notation "Ω" => Quotient <| orbitRel G X

variable {G}

/-- A bijection between the orbits under the action of a subgroup `H` on `X`, and the orbits
under the action of `H` on each orbit under the action of `G`. -/
@[to_additive /-- A bijection between the orbits under the action of an additive subgroup `H` on
`X`, and the orbits under the action of `H` on each orbit under the action of `G`. -/]
noncomputable def equivSubgroupOrbits (H : Subgroup G) :
    orbitRel.Quotient H X ≃ Σ ω : Ω, orbitRel.Quotient H (orbitRel.Quotient.orbit ω) :=
  (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm.trans
    (Equiv.sigmaCongrRight fun ω ↦ (equivSubgroupOrbitsSetoidComap H ω).symm)

end MulAction
end
