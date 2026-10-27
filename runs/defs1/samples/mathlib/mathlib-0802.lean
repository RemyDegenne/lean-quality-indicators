@[expose] public section

open Function Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) and
open source is a `PartialHomeomorph`. -/
@[simps! toPartialEquiv]
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.domRestrict hs)

end PartialHomeomorph
end
