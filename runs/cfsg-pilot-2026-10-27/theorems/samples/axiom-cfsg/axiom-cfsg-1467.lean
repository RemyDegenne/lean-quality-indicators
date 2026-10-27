public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS

open CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS

open CFSG.RankThree.PartTwo.Sec21.FF79.AS

open CFSG CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

variable {b : G} {J B A P D S : Subgroup G}

namespace AStarCtx

variable (c : AStarCtx b J B A P D S)

include c

section Z

variable {z : D} (hz : z ∈ Subgroup.center D) (hz1 : z ≠ 1)

include hz hz1

theorem As_comm {s t : G} (hs : s ∈ c.As) (ht : t ∈ c.As) : s * t = t * s := by
  have e1 := c.z_inv_As hz hz1 (c.As.mul_mem hs ht)
  have e2 : (z : G) * (s * t) * (z : G)⁻¹ = s⁻¹ * t⁻¹ := by
    rw [← c.z_inv_As hz hz1 hs, ← c.z_inv_As hz hz1 ht]; group
  rw [e1, mul_inv_rev] at e2
  have := congrArg (·⁻¹) e2
  simpa [mul_inv_rev] using this

end Z
end AStarCtx
end CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
end
