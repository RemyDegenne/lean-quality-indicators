public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace TopCat.Sheaf.SquareTransition

variable (A : Type u) [Category.{w} A]

variable {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]

variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {Xj Xi Yj Yi : TopCat.{w}}

theorem adjoint_composite {Xk : TopCat.{w}}
    (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A} {H : Xk.Sheaf A}
    (aij : (pullback A pij).obj F ⟶ G)
    (ajk : (pullback A pjk).obj G ⟶ H) :
    adjoint A (pjk ≫ pij) (composite A pjk pij aij ajk) =
      adjoint A pij aij ≫ (pushforward A pij).map (adjoint A pjk ajk) := by
  let adjComp := (pullbackPushforwardAdjunction A pij).comp
    (pullbackPushforwardAdjunction A pjk)
  let adjDirect : pullback A (pjk ≫ pij) ⊣
      (pushforward A pjk ⋙ pushforward A pij) :=
    pullbackPushforwardAdjunction A (pjk ≫ pij)
  change adjDirect.homEquiv F H
    ((Adjunction.leftAdjointUniq adjComp adjDirect).inv.app F ≫
      ((pullback A pjk).map aij ≫ ajk)) = _
  rw [adjDirect.homEquiv_naturality_right]
  rw [Adjunction.leftAdjointUniq_inv_app]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← adjComp.homEquiv_unit]
  rw [Adjunction.comp_homEquiv]
  change
    ((pullbackPushforwardAdjunction A pij).homEquiv F
      ((pushforward A pjk).obj H))
      (((pullbackPushforwardAdjunction A pjk).homEquiv
        ((pullback A pij).obj F) H)
        ((pullback A pjk).map aij ≫ ajk)) =
      ((pullbackPushforwardAdjunction A pij).homEquiv F G) aij ≫
      (pushforward A pij).map
        (((pullbackPushforwardAdjunction A pjk).homEquiv G H) ajk)
  rw [(pullbackPushforwardAdjunction A pjk).homEquiv_naturality_left]
  rw [(pullbackPushforwardAdjunction A pij).homEquiv_naturality_right]

end TopCat.Sheaf.SquareTransition
end
end
