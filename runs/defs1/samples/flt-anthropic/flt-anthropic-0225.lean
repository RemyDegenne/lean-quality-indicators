set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.RelPicard.BaseTransport

variable {R : Type u} [CommRing R]

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

namespace BaseChange

variable (R' : Type u) [CommRing R'] [Algebra R R']

def ofR_mapIso {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {M M' : RigidifiedLineBundle c ε (t' ≫ specMap R R')} (e : M.L ≅ M'.L) :
    (BaseChange.ofR c ε R' M).L ≅ (BaseChange.ofR c ε R' M').L :=
  (Scheme.Modules.pullback (BaseChange.κ c R' t').hom).mapIso e

end BaseChange
end AlgebraicGeometry.RelPicard.BaseTransport
end
