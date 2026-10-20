@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

theorem faithfullyFlatTestMorphisms_isStableUnderBaseChange :
    (faithfullyFlatTestMorphisms K).IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g f' g' hs hg
  have hs' := isPushout_commRingCat_of_fgAlgCat K f.unop g.unop
    g'.unop f'.unop hs.unop
  haveI : (RingHom.toMorphismProperty @RingHom.FaithfullyFlat).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.FaithfullyFlat.isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := RingHom.toMorphismProperty @RingHom.FaithfullyFlat) hs' hg

end General
end AlgebraicGeometry
end
