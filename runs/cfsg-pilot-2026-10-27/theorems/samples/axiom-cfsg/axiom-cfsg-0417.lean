public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.FourthResidue CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
  CFSG.LieType.Chevalley.RootOps

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_split_conj_stdLevi
    {E : Type*} [Group E] [Finite E] (η : E →* stdGroup)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (g : stdGroup) :
    ∃ F : Subgroup E, F.map η = leviG.map (MulAut.conj g).toMonoidHom ∧
      (∀ x ∈ F, η x = 1 → x = 1) ∧ F ⊓ η.ker = ⊥ ∧
      (leviG.map (MulAut.conj g).toMonoidHom).comap η = F ⊔ η.ker :=
  exists_split_of_mulEquiv _ ((leviG.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans leviGEquiv) η hη hC h2

end CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover
end
