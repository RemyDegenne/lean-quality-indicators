@[expose] public section

namespace CategoryTheory

namespace Idempotents

open Category Karoubi CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

variable (C D E)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical functor `(C ⥤ Karoubi D) ⥤ (Karoubi C ⥤ Karoubi D)` -/
@[simps]
def functorExtension₁ : (C ⥤ Karoubi D) ⥤ Karoubi C ⥤ Karoubi D where
  obj := FunctorExtension₁.obj
  map := FunctorExtension₁.map
  map_id F := by
    ext P
    exact comp_p (F.map P.p)
  map_comp {F G H} φ φ' := by
    ext P
    simp only [comp_f, FunctorExtension₁.map_app_f, NatTrans.comp_app, assoc]
    have h := φ.naturality P.p
    have h' := F.congr_map P.idem
    simp only [hom_ext_iff, comp_f, F.map_comp] at h h'
    slice_rhs 2 3 => rw [← h]
    slice_rhs 1 2 => rw [h']
    simp only [assoc]

end Idempotents
end CategoryTheory
end
