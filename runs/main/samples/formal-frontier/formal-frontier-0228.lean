set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma degreeOneIso_natural (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    TopModuleCat.ofHom (crossedQuotientMap q) ≫ (degreeOneIso B).hom =
      (degreeOneIso A).hom ≫ map (ContinuousMonoidHom.id G) q 1 := by
  apply (cancel_mono (homologyQuotientIso B).hom).1
  rw [degreeOneIso, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, homologyQuotientIso_natural, ← Category.assoc,
    degreeOneIso, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]

end ContinuousCohomology
end
