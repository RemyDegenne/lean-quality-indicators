public section

open Filter Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

variable (A) [IsTopologicalRing A] in
/-- A *Huber pair* `(A, A⁺)`: a Huber ring together with a ring of integral elements. Only the
noncanonical subring `A⁺` is stored; the Huber structure on `A` is a parameter. -/
structure Pair [IsHuberRing A] where
  /-- The ring of integral elements `A⁺`. -/
  plus : Subring A
  /-- `A⁺` really is a ring of integral elements. -/
  isRingOfIntegralElements : IsRingOfIntegralElements plus

end TauCeti.Huber
end
