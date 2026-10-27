public section

universe u v

namespace CategoryTheory.Limits.SingleObj

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {G : Type*} [Monoid G] [Fintype G]
  {J : SingleObj G ⥤ C} (c : Cocone J) (t : c.pt ⟶ J.obj (SingleObj.star G))

/-- Let `G` be a finite monoid acting on an object of a preadditive category, and let `c` be a
cocone over the action whose leg `π` has a *transfer* `t`: `t ≫ π = |G| • 𝟙` and
`π ≫ t = ∑_{g ∈ G} J.map g`. If multiplication by `|G|` is invertible on the acted-on object and on
the cocone point, then `c` is a colimit cocone: the cocone point is the object of coinvariants. -/
noncomputable def isColimitOfTransfer
    (ht : t ≫ c.ι.app (SingleObj.star G) = Fintype.card G • 𝟙 c.pt)
    (ht' : c.ι.app (SingleObj.star G) ≫ t = ∑ g : G, J.map g)
    [IsIso (Fintype.card G • 𝟙 (J.obj (SingleObj.star G)))] [IsIso (Fintype.card G • 𝟙 c.pt)] :
    IsColimit c where
  desc s := t ≫ inv (Fintype.card G • 𝟙 _) ≫ s.ι.app (SingleObj.star G)
  fac s j := by
    obtain rfl : j = SingleObj.star G := rfl
    rw [← Category.assoc, ht', reassoc_of% Preadditive.comp_inv_nsmul_id, IsIso.inv_comp_eq]
    simp [Preadditive.sum_comp, Preadditive.nsmul_comp, s.w]
  uniq s m hm := by
    have key : inv (Fintype.card G • 𝟙 _) ≫ c.ι.app (SingleObj.star G) =
        c.ι.app (SingleObj.star G) ≫ inv (Fintype.card G • 𝟙 c.pt) :=
      (Preadditive.comp_inv_nsmul_id (Y := c.pt) _ _).symm
    conv_rhs => rw [← hm (SingleObj.star G), reassoc_of% key, reassoc_of% ht,
      IsIso.hom_inv_id_assoc]

end Preadditive
end CategoryTheory.Limits.SingleObj
end
