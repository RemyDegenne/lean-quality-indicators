set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Scheme.Modules

def IsSectionBasisOn {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    (V : X.Opens) {m : ℕ} (σ : Fin m → Γ(M, V)) : Prop :=
  Function.Bijective fun c : Fin m → S =>
    ∑ i, ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) • σ i

end Scheme.Modules
end AlgebraicGeometry
end
