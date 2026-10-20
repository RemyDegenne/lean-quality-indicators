@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

variable {G}

variable {P : ProfiniteGrp.{max u v}}

theorem lift_unique (f g : product G ⟶ P)
    (h : eta G ≫ (forget₂ _ _).map f =
      eta G ≫ (forget₂ _ _).map g) : f = g := by
  ext x
  apply congrFun
  refine (denseRange G).equalizer f.hom.continuous_toFun
    g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using! (ConcreteCategory.congr_hom h y)

end ProfiniteGrp.FreeProduct
end
