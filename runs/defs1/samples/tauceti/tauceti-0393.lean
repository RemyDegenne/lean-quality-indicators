public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X S' X' : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X} {π' : X' ⟶ S'} {zero' : S' ⟶ X'}
  {g : X' ⟶ X} {f : S' ⟶ S} (hg : IsPullback g π' π f)
  {k : PointedWeierstrassChart π' zero'} {c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap ≫ f)

/-- Let `g : X' ⟶ X` be the base change of `π : X ⟶ S` along `f : S' ⟶ S`, and let `k` and `c` be
pointed Weierstrass charts of `π'` and `π` whose bases are related by `h : k.base ⟶ c.base` over
`f`. This is the morphism from the restriction of `X'` to the base of `k` to the restriction of `X`
to the base of `c` induced by `g`, lying over `h`. It generalizes `pullbackCarrierMap`, the case
`f = 𝟙 S` and `g = 𝟙 X`. -/
noncomputable def carrierMap : k.pullbackCarrier ⟶ c.pullbackCarrier :=
  c.isPullback.lift (k.toTotal ≫ g) (k.toBase ≫ h) (by
    rw [Category.assoc, hg.w, reassoc_of% k.isPullback.w, Category.assoc, hh])

end PointedWeierstrassChart
end TauCeti.AlgebraicGeometry
end
