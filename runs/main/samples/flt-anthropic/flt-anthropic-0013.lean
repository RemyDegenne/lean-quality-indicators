namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TwoPresSol

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
  (𝔓 : Scheme.Modules.ProjPresentation M f N)

variable {M' : X.Modules} (𝔔 : Scheme.Modules.ProjPresentation M' f N) (h : 𝔓.toProj = 𝔔.toProj)

theorem app_map {P Q : X.Modules} (φ : P ⟶ Q) {V V' : X.Opens} (hle : V' ≤ V) (x : Γ(P, V)) :
    Q.presheaf.map (homOfLE hle).op (φ.app V x) = φ.app V' (P.presheaf.map (homOfLE hle).op x) := by
  have := φ.mapPresheaf.naturality (homOfLE hle).op
  have e := congrArg (fun f => f x) this
  simpa using e.symm

end TwoPresSol
end P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq
