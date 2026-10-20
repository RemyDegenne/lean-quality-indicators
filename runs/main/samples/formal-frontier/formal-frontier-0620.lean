set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

attribute [local instance] jointlyContinuous_mackeyStabilizer

variable (X : TopRep.{max v w} k G)

set_option maxHeartbeats 800000 in
-- Comparing the crossed and cocycle maps expands the conjugation and restriction squares.
lemma cocyclesOneCrossedIso_mackey (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace H]
    [LocallyCompactSpace K]
    [LocallyCompactSpace (mackeyOpenStabilizer H K x)] :
    cocyclesMap (mackeyStabilizerToLeft H K x)
          (mackeyCoefficientHom X H K x) 1 ≫
        (cocyclesOneCrossedIso
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))).hom =
      (cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom ≫
        TopModuleCat.ofHom (mackeyConjugateCrossed X H K x) := by
  ext σ l
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    ConcreteCategory.hom_ofHom]
  change
    (((cocyclesOneCrossedIso
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X))).hom
      (cocyclesMap (mackeyStabilizerToLeft H K x)
        (mackeyCoefficientHom X H K x) 1 σ)).1 l) =
      (mackeyConjugateCrossed X H K x
        ((cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom σ)).1 l
  rw [cocyclesOneCrossedIso_hom_apply, mackeyConjugateCrossed_apply,
    cocyclesOneCrossedIso_hom_apply]
  have hh := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (mackeyStabilizerToLeft H K x)
        (mackeyCoefficientHom X H K x)) 1) σ
  simp only [ConcreteCategory.comp_apply] at hh
  change
    (((HomologicalComplex.iCycles
        (TopRep.homogeneousCochains
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))) 1)
      ((HomologicalComplex.cyclesMap
        (cochainsMap (mackeyStabilizerToLeft H K x)
          (mackeyCoefficientHom X H K x)) 1) σ)).1 1 l) = _
  refine (congrArg (fun τ => τ.1 1 l) hh).trans ?_
  exact cochainsMap_one_apply (mackeyStabilizerToLeft H K x)
    (mackeyCoefficientHom X H K x)
    ((TopRep.homogeneousCochains (TopRep.res H.subtype X)).iCycles 1 σ) l

end CorestrictionTransversal
end ContinuousCohomology
end
end
