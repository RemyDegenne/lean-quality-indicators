set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

lemma cocyclesOneCrossedIso_natural (q : A ⟶ B) :
    cocyclesMap (ContinuousMonoidHom.id G) q 1 ≫
        (cocyclesOneCrossedIso B).hom =
      (cocyclesOneCrossedIso A).hom ≫ TopModuleCat.ofHom (crossedMap q) := by
  ext σ g
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    ConcreteCategory.hom_ofHom, crossedMap_apply]
  rw [cocyclesOneCrossedIso_hom_apply, cocyclesOneCrossedIso_hom_apply]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) q) 1) σ
  exact congrArg (fun τ => τ.1 1 g) h

end ContinuousCohomology
end
