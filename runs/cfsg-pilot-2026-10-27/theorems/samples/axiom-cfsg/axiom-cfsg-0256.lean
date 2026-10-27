public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18 (le_pCoreOf_of_normal)

open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.LieType.ChevTwo (Chev2CoreCent Chev2KDOut autCentralizer)

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

open scoped commutatorElement

section Construction

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

variable (K)

variable {K} {D1 : Subgroup ↥(Subgroup.normalizer (K : Set X))}

theorem Gam1_le_centralizer (hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a)
    {d : ↥(Subgroup.normalizer (K : Set X))} (hd : d ∈ D1) :
    Gam1 K D1 ≤ Subgroup.centralizer ({d} : Set ↥(Subgroup.normalizer (K : Set X))) :=
  sup_le (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd))
    (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (hab e he d hd))

end Construction
end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
end
