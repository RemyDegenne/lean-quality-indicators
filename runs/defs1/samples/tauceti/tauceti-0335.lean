public section

namespace TauCeti

open Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

section Dominant

variable {R : Type u} [CommRing R] [CharZero R] {N : ℕ} {mu : Fin N → R}

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

namespace glTraceTwistedYoungWedge

variable (R) in
/-- **A trace-twisted Young wedge has the exterior power as its underlying `R`-module.** Every
statement about the carrier is made against this equivalence, so that the definition is not
unfolded. -/
def linearEquiv (a : ι → ℕ) (c : R) :
    glTraceTwistedYoungWedge R a c ≃ₗ[R] ⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R) :=
  GlTraceTwist.linearEquiv ι c _

end glTraceTwistedYoungWedge
end Dominant
end TauCeti
end
