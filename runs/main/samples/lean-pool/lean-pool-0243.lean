@[expose] public section

namespace HsVirial

open Set

open Metric

open MeasureTheory

open scoped BigOperators ENNReal

noncomputable section

lemma hardSphere_nbc_region_subset_forkPackingSeparatedRegion
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := 3)) T ⊆
      hardSphereForkPackingSeparatedRegion P := by
  intro r hr f hf
  exact hardSphere_treeRegion_mem_separatedPair_of_mem_forkAvoidance hP
    (hardSphere_nbc_region_subset_tree_region hr)
    (hardSphere_nbc_region_subset_forkAvoidance hP hr) hf

end
end HsVirial
end
