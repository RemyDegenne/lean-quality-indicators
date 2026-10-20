@[expose] public section

open Opposite CategoryTheory Limits

noncomputable section

universe u v₁ v₂ v₃ u₁ u₂ u₃

section ModelsForLocalCohomology

open localCohomology

variable {R : Type u} [CommRing R]

/-- Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` with radical
containing `J`. -/
def localCohomology.ofSelfLERadical (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram.{u} (selfLERadicalDiagram.{u} J) i

end ModelsForLocalCohomology
end
end
