open Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-- Wedhorn's topological localisation: the topology on `Aₛ` whose neighbourhoods of zero are the
images of the powers of `J = I · D`, the candidate ideal of definition of
`D = A₀[T/s]`. Only separate continuity of multiplication on `A` is needed;
addition on `A` need not be continuous. -/
@[instance_reducible] noncomputable def locTopology [SeparatelyContinuousMul A]
    (P : PairOfDefinition A)
    (T : Set A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    TopologicalSpace S :=
  (locBasis P T s S hden).topology

end PairOfDefinition
end
end TauCeti.Huber
