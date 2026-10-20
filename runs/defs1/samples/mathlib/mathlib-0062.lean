@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃ u

open Function CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

namespace MonObj

variable {M X Y : C} [MonObj M]

@[inherit_doc] scoped notation "μ" => MonObj.mul

@[inherit_doc] scoped notation "μ[" M "]" => MonObj.mul (X := M)

@[inherit_doc] scoped notation "η" => MonObj.one

@[inherit_doc] scoped notation "η[" M "]" => MonObj.one (X := M)

/-- Transfer `MonObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[to_additive (attr := simps! -isSimp, instance_reducible)
/-- Transfer `AddMonObj` along an isomorphism. -/]
def ofIso (e : M ≅ X) : MonObj X where
  one := η[M] ≫ e.hom
  mul := (e.inv ⊗ₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (λ_ X).inv]
    simp only [comp_whiskerRight, tensorHom_def, Category.assoc,
      hom_inv_whiskerRight_assoc]
    simp [← tensorHom_def_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv]
    simp only [MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
      whiskerLeft_hom_inv_assoc, Iso.inv_hom_id]
    simp [← tensorHom_def'_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  mul_assoc := by simpa [← id_tensorHom, ← tensorHom_id,
      -associator_conjugation, associator_naturality_assoc] using
      congr(((e.inv ⊗ₘ e.inv) ⊗ₘ e.inv) ≫ $(MonObj.mul_assoc M) ≫ e.hom)

end MonObj
end CategoryTheory
end
