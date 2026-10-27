@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C}

namespace CategoryTheory.Limits

section Under

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- A binary cofan in `Under X` is a colimit if its corresponding pushout cocone from `X` is a
colimit. -/
-- `IsColimit.ofCoconeEquiv` isn't used here because the lift it defines is `pushout.desc ≫ 𝟙 _`.
-- TODO: Define `IsColimit.copy`?
@[simps!]
def IsColimit.pushoutCoconeEquivBinaryCofanFunctor {c : PushoutCocone f g} (hc : IsColimit c) :
    IsColimit <| pushoutCoconeEquivBinaryCofan.functor.obj c :=
  BinaryCofan.isColimitMk
    (fun s ↦ Under.homMk
      (hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.trans s.inr.w.symm))) <| by
        simpa using! s.inl.w)
    (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _)) (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ ↦ by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using! congr(($e₁).right)
    · simpa using! congr(($e₂).right)

end Under
end CategoryTheory.Limits
end
