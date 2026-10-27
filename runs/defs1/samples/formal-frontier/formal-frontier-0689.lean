set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- A continuous commutative square induces a continuous map on quotients by
the two compact ranges. -/
@[expose] noncomputable def quotientRangeMap {X Y X' Y' : CompHausAddCommGrp.{u}}
    (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x, g (p x) = q (f x)) : quotientRange f ⟶ quotientRange g := by
  let φ : Y →+ quotientRange g :=
    (QuotientAddGroup.mk' g.hom.range).comp q.hom.toAddMonoidHom
  have hφ : f.hom.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    change QuotientAddGroup.mk' g.hom.range (q (f x)) = 0
    rw [← h x, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    exact ⟨p x, rfl⟩
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom := QuotientAddGroup.lift f.hom.range φ hφ
      continuous_toFun := ?_ }
  apply continuous_coinduced_dom.2
  exact (quotientRangeπ g).hom.continuous.comp q.hom.continuous

end CompHausAddCommGrp
end
