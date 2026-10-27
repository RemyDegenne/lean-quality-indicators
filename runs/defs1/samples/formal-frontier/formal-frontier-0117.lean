@[expose] public section

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

open CategoryTheory.CartesianMonoidalCategory

open CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The automorphism `(x, y) ↦ (x, x⁻¹y)` of the product of a group object with
itself. It implements the diagonal-to-unit argument of Milne,
*Algebraic Groups* (2017), Proposition 1.22 in a Cartesian category. -/
def leftDivIso (G : C) [GrpObj G] : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G) (lift (fst G G ≫ ι) (snd G G) ≫ μ)
  inv := lift (fst G G) (lift (fst G G) (snd G G) ≫ μ)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc]
      simp only [lift_fst, lift_snd]
      rw [← GrpObj.eq_lift_inv_left]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc]
      simp only [lift_fst_assoc, lift_snd]
      rw [GrpObj.lift_inv_left_eq]

end CategoryTheory.GrpObj
end
