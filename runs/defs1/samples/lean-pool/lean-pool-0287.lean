@[expose] public section

noncomputable section

namespace SphereOddDegree

open CategoryTheory unitInterval

/-- The genuine monodromy action of the fundamental group `π₁(RP n, x)` on the
two-element fibre of the double cover, obtained by transporting the canonical
`MulAction (Equiv.Perm _) _` along `projMonodromyHom`. This is the
fundamental-group action that *Route A* toward `H¹(RPⁿ; F₂)` requires; it is
provided as a `def` (not a global `instance`) so as not to pollute typeclass
resolution. -/
@[instance_reducible]
def projMonodromyMulAction (n : ℕ) (x : RP n) :
    MulAction (FundamentalGroup (RP n) x) (proj n ⁻¹' {x}) :=
  MulAction.compHom _ (projMonodromyHom n x)

end SphereOddDegree
end
end
