public section

namespace TauCeti

open Metric Set Topology

variable {M N N' P F F' : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
  [TopologicalSpace P] [TopologicalSpace F] [TopologicalSpace F']

variable {φ : OpenPartialHomeomorph M F} {S : Set F} {A : Set M}

namespace IsSliceChart

section ZeroSlice

variable {X Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Y'] [Zero Y'] {e : OpenPartialHomeomorph X (Y × Y')} {s : Set X}

/-- Restrict an ambient zero-slice chart to the flattened set and retain its tangential
coordinate. -/
noncomputable def subtypeChart
    (h : IsSliceChart e ((univ : Set Y) ×ˢ ({0} : Set Y')) s) [Nonempty s] :
    OpenPartialHomeomorph s Y :=
  e.subtypeCoord s inferInstance (fun y : Y => (y, (0 : Y'))) Prod.fst h.symm_mk_zero_mem
    h.mk_fst_zero_eq (fun _ _ => rfl) (continuous_id.prodMk continuous_const)
    continuous_fst.continuousOn

end ZeroSlice
end IsSliceChart
end TauCeti
end
