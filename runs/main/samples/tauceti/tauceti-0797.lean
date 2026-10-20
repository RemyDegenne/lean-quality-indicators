public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X S' X' : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X} {π' : X' ⟶ S'} {zero' : S' ⟶ X'}
  {g : X' ⟶ X} {f : S' ⟶ S} (hg : IsPullback g π' π f)
  {k : PointedWeierstrassChart π' zero'} {c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap ≫ f)

theorem projModelZero_modelMap (h0 : zero' ≫ g = f ≫ zero) :
    k.equation.projModelZero ≫ modelMap hg hh =
      (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ c.equation.projModelZero := by
  rw [← cancel_epi k.baseIso.hom, ← k.modelIso_zero_assoc]
  simp [modelMap, pulledZero_carrierMap_assoc hg hh h0]

end PointedWeierstrassChart
end TauCeti.AlgebraicGeometry
end
