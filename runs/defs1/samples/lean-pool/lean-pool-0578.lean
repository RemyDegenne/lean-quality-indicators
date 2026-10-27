@[expose] public section

namespace Utilities.Certificate.CoreOrbitReduction

open Utilities.Certificate

open Utilities

open ExplicitPotential

open SubdivisionGraph

universe u v w

variable {n p : ℕ}

namespace CoreSymmetry

variable {core : ExplicitPotential.Core n p}

/-- **The kernel-transparent constructor.**

`ofMaps` is the convenient one — it checks bijectivity by injectivity — but it
builds its permutations with `Equiv.ofBijective`, and `Equiv.symm` of such a
permutation does **not** reduce in the kernel.  Forward application still
reduces (`ofMaps_vertexPerm` and `ofMaps_slotPerm` above are both `rfl`), so a
`decide` about `vertexPerm` cannot tell the two constructions apart.  What
breaks is `reindexLength`, which is `fun edge => length (slotPerm.symm edge)`,
and with it every consumer of it — `ClosedCoreSymmetry.targetLength` and the
closed-orthant orbit and chamber arguments.

`ofInverses` takes the two inverse functions explicitly, so every projection,
forward and backward, reduces.  **Use it whenever the symmetry will be fed to
`reindexLength`**; `reindexLength_ofInverses` below is the one-line regression
test that the reduction is really there. -/
def ofInverses (core : ExplicitPotential.Core n p)
    (vertexMap vertexInv : Fin n → Fin n) (slotMap slotInv : Fin p → Fin p)
    (reversed : Fin p → Bool)
    (hVertexLeft : ∀ x, vertexInv (vertexMap x) = x)
    (hVertexRight : ∀ x, vertexMap (vertexInv x) = x)
    (hSlotLeft : ∀ e, slotInv (slotMap e) = e)
    (hSlotRight : ∀ e, slotMap (slotInv e) = e)
    (hTail : ∀ edge : Fin p, core.tail (slotMap edge) =
      if reversed edge then vertexMap (core.head edge) else vertexMap (core.tail edge))
    (hHead : ∀ edge : Fin p, core.head (slotMap edge) =
      if reversed edge then vertexMap (core.tail edge) else vertexMap (core.head edge)) :
    CoreSymmetry core where
  vertexPerm := ⟨vertexMap, vertexInv, hVertexLeft, hVertexRight⟩
  slotPerm := ⟨slotMap, slotInv, hSlotLeft, hSlotRight⟩
  reversed := reversed
  tail_eq := hTail
  head_eq := hHead

end CoreSymmetry
end Utilities.Certificate.CoreOrbitReduction
end
