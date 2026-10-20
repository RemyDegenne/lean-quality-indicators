public section

noncomputable section

open CategoryTheory Limits Opposite

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  (M : ModuleCat.{max v w} R) {X : TopCat.{v}}

section Homotopy

variable {Y : TopCat.{v}} {f g : X ⟶ Y} (H : f.hom.Homotopy g.hom)
  (L : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- Homotopic pullbacks of a local coefficient system have canonically isomorphic twisted
cohomology groups. -/
def twistedCohomologyPullbackHomotopyIso (n : ℕ) :
    ((pullback g.hom).obj L).twistedCohomology k M n ≅
      ((pullback f.hom).obj L).twistedCohomology k M n :=
  twistedCohomologyCoefficientIso k M ((pullbackHomotopyIso H).app L) n

end Homotopy
end LocalCoefficientSystem
end TauCeti
end
end
