public section

open Set

open Bundle

open Topology

namespace TauCeti

variable {B F N : Type*} {E : B → Type*}

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [TopologicalSpace N]

namespace IsTubularNeighborhood

variable {f : B → N} {U : Set (TotalSpace F E)} {toFun : U → N}

/-- The radial contraction of a tubular neighborhood, with its image kept in
the tubular domain by `fiberwise_starConvex`. -/
def radialContraction (T : IsTubularNeighborhood f U toFun) : Icc (0 : ℝ) 1 × U → U :=
  fun p => ⟨⟨p.2.1.1, (p.1 : ℝ) • p.2.1.2⟩,
    by
      simpa using (T.fiberwise_starConvex p.2.1.1).smul_mem p.2.property
        p.1.2.1 p.1.2.2⟩

end IsTubularNeighborhood
end TauCeti
end
