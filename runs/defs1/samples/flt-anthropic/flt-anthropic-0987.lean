namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart

set_option autoImplicit false

p2m_open

namespace GrassH2

universe u

variable (R : Type) [CommRing R]

variable {R}

variable {ι : Type} {S : ι → Type} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] (X : Ctx R ι S)

namespace Ctx

noncomputable def u (i : ι) : {s : X.F (S i) // X.P i (S i) s} := (X.chart i (S i)).symm (AlgHom.id R (S i))

end Ctx
end GrassH2
end P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
