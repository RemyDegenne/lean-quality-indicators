public section

set_option warningAsError true

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

attribute [instance] IsLocallyNormalRing.isDomain_atPrime
  IsLocallyNormalRing.isIntegrallyClosed_atPrime

namespace AlgebraicGeometry

variable (X : Scheme.{u})

attribute [instance] IsNormal.stalk_isDomain IsNormal.stalk_isIntegrallyClosed

theorem isIntegrallyClosed_stalk_of_specializes {x y : X} (hxy : x ⤳ y)
    [_root_.IsDomain (X.presheaf.stalk y)]
    [_root_.IsIntegrallyClosed (X.presheaf.stalk y)] :
    _root_.IsIntegrallyClosed (X.presheaf.stalk x) := by
  let i := X.affineCover.idx y
  let f := X.affineCover.f i
  let U : X.Opens := f.opensRange
  have hyU : y ∈ U := by
    obtain ⟨y', hy'⟩ := X.affineCover.covers y
    exact ⟨y', hy'⟩
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let q := hU.primeIdealOf ⟨y, hyU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    exact ((subtype_specializes_iff _ _).mpr hxy).map hU.isoSpec.hom.continuous
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.isIntegrallyClosed_of_le
    (R := Γ(X, U)) (X.presheaf.stalk y) (X.presheaf.stalk x)
    (p := p.asIdeal) (q := q.asIdeal) hpq

end AlgebraicGeometry
end
