public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smul_mem_starSet_iff (w : WeylGroup TwistTag.E6.tag)
    {y : Fin TwistTag.E6.tag.rank → ZMod 3} {g δ : Fin TwistTag.E6.tag.rank → ℤ} :
    w • δ ∈ starSet y (w • g) ↔ δ ∈ starSet (weylDual w y) g := by
  simp only [starSet, Set.mem_setOf_eq, isRoot_smul_iff, dot3_smul, iform_smul]

end CFSG.StandardType.TwE6NormThree
end
