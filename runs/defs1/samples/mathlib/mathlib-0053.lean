@[expose] public section

universe w' w u v

open CategoryTheory Category Limits

variable {R : Type w} [Ring R]

namespace ModuleCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ ModuleCat.{w'} R)

namespace HasColimit

variable [HasColimit (F ⋙ forget₂ _ AddCommGrpCat)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)` is a colimit cocone. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) where
  desc s := homMk (colimit.desc _ ((forget₂ _ AddCommGrpCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [mkOfSMul_smul]
    dsimp
    simp only [ι_colimMap_assoc, Functor.comp_obj, forget₂_obj, colimit.ι_desc,
      Functor.mapCocone_pt, Functor.mapCocone_ι_app, forget₂_map]
    exact smul_naturality (s.ι.app j) r)
  fac s j := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    exact colimit.ι_desc ((forget₂ _ AddCommGrpCat).mapCocone s) j
  uniq s m hm := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc ((forget₂ _ AddCommGrpCat).mapCocone s) j]
    dsimp
    rw [← hm]
    rfl

end HasColimit
end ModuleCat
end
