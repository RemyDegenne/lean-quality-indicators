public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Degree `-1` Tate cohomology is the kernel of the norm from coinvariants to
invariants. -/
noncomputable def tateCohomologyNegOneIsoKernelNorm (M : Rep R G) :
    tateCohomology M (-1) ≅ kernel (normFromCoinvariants M) :=
  IsLimit.conePointUniqueUpToIso ((normSequence_exact M).exact 0).fIsKernel
    (limit.isLimit (parallelPair (normFromCoinvariants M) 0))

end FiniteGroupTateCohomology
end
