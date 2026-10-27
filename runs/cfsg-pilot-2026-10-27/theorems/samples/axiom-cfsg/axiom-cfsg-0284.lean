public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.RankThree.Lattice

open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec chainRoot chain134
  support134 IsNegativeTransition)

open scoped Matrix

theorem e6Four_stab_of_fixed {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf (q : ZMod p) = 4) (hΦ : (q : ZMod p) ^ 2 + 1 = 0)
    {a : Fin Tag.E6.rank → Lˣ} (ha : a ∈ fixedCharTuples e6FourM Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E6)) :=
  rootCharStabilizer_subset_closure_of_fixed e6FourM Fr hFr hp ha hap ha1
    (fun _ hz hzM => e6Four_dual_stab_le_closure hp (e6Four_p_cases hp hp3 hord) hΦ hz hzM)

end CFSG.RankThree.PartOne.KE
end
