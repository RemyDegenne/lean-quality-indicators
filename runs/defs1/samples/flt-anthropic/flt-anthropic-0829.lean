namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections

set_option autoImplicit false

noncomputable section

universe u

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace TwoAffineOpenCover

p2m_open

namespace UnitComparison

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

def toFunH0 (x : (SU 𝒱 c).H0) : (SO 𝒱 c).H0 :=
  ⟨(show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from x.1), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← cechDiff_eq, hx]; rfl⟩

end UnitComparison
end TwoAffineOpenCover
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
