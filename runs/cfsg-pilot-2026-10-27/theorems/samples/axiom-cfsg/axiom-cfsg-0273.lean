public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

open scoped commutatorElement

namespace T7Q

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

open T7F2 T7G2 T7DR

section Basic

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem z_eq_pow {a b : G} {n : ℕ} (c : QuatCoord R a b n) : z = a ^ (2 ^ n) := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.z_eq_pow_gen h.hzR c

end Basic
end T7Q
end CFSG.ClassicalInvolution.Asc77
end
