@[expose] public section

universe s t w v u

namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C]

variable {J : Type*} {I : J → Type*} [Category* J] [∀ j, Category (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

section Small

variable {J : Type w} {I : J → Type w} [SmallCategory J] [∀ j, SmallCategory (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

set_option backward.defeqAttrib.useBackward true in
/-- If `P` is a colimit presentation over `J` of `X` and for every `j` we are given a colimit
presentation `Qⱼ` over `I j` of the `P.diag.obj j`, this is the refined colimit presentation of `X`
over `Total Q`. -/
@[simps]
def bind {X : C} (P : ColimitPresentation J X) (Q : ∀ j, ColimitPresentation (I j) (P.diag.obj j))
    [∀ j, IsFiltered (I j)] [∀ j i, IsFinitelyPresentable.{w} ((Q j).diag.obj i)] :
    ColimitPresentation (Total Q) X where
  diag.obj k := (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  ι.app k := (Q k.1).ι.app k.2 ≫ P.ι.app k.1
  ι.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
          ι.naturality {i i'} u := by
            let v : Total.mk Q j i ⟶ .mk _ j i' := { base := 𝟙 _, hom := (Q _).diag.map u }
            simpa using c.ι.naturality v }
      ι.naturality {j j'} u := by
        refine (Q j).isColimit.hom_ext fun i ↦ ?_
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          (Q j).isColimit.fac]
        obtain ⟨i', hom, rfl⟩ := Total.exists_hom_of_hom (P := Q) i u
        rw [reassoc_of% hom.w, (Q j').isColimit.fac]
        simpa using c.ι.naturality hom }
  isColimit.fac := fun c ⟨j, i⟩ ↦ by simp [P.isColimit.fac, (Q j).isColimit.fac]
  isColimit.uniq c m hm := by
    refine P.isColimit.hom_ext fun j ↦ ?_
    simp only [P.isColimit.fac]
    refine (Q j).isColimit.hom_ext fun i ↦ ?_
    simpa [(Q j).isColimit.fac] using hm (.mk _ j i)

end Small
end CategoryTheory.Limits.ColimitPresentation
end
