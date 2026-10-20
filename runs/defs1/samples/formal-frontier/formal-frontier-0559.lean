@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace PrimeSpectrum

variable {J : Type v} [SmallCategory J]

variable (F : J ⥤ CommRingCat.{max v u}) (c : Cocone F)

/-- Compatible tuples of prime ideals in a ring diagram, viewed as sections of spectra. -/
abbrev spectrumSections (F : J ⥤ CommRingCat.{max v u}) :=
  ((F.op ⋙ AlgebraicGeometry.Spec.toTop) ⋙ forget TopCat).sections

end PrimeSpectrum
end
