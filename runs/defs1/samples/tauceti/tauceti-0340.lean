open Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-- The candidate ideal of definition `J = I · D` in `D`. -/
noncomputable def locIdeal (P : PairOfDefinition A) (T : Set A)
    (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] : Ideal (locSubring P T s S) :=
  Ideal.map (toLocSubring P T s S) P.idealOfDefinition

end PairOfDefinition
end
end TauCeti.Huber
