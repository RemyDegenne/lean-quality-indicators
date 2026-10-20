public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

@[reassoc (attr := simp)]
lemma cokernelπ_covariantCokernelIso_hom
    {S : ShortComplex C} (hS : S.ShortExact) (X : C)
    [Subsingleton (Ext X S.X₂ 1)] :
    cokernel.π (AddCommGrpCat.ofHom
        ((mk₀ S.g).postcomp X (add_zero 0))) ≫
      (covariantCokernelIso hS X).hom =
        AddCommGrpCat.ofHom (hS.extClass.postcomp X rfl) := by
  dsimp [covariantCokernelIso]
  apply colimit.isoColimitCocone_ι_hom

end CategoryTheory.Abelian.Ext
end
end
