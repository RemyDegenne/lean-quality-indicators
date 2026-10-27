namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing

set_option autoImplicit false

universe u

p2m_open

noncomputable section

namespace F6ea14e94

open Opposite DirectSum

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)

scoped instance (n : ℕ) : AddCommGroup (Sec f L n) := inferInstanceAs (AddCommGroup Γ(L.tensorPow n, ⊤))

scoped instance (n : ℕ) : Module Γ(X, ⊤) (Sec f L n) := inferInstanceAs (Module Γ(X, ⊤) Γ(L.tensorPow n, ⊤))

scoped instance (n : ℕ) : Module S (Sec f L n) := Module.compHom (Sec f L n) (baseHom f)

def mulSec {m n : ℕ} (a : Sec f L m) (b : Sec f L n) : Sec f L (m + n) :=
  ((tensorPowAdd L m n).hom.app ⊤ (tensorSections (L := L.tensorPow m) (M := L.tensorPow n) a b) :
    Γ(L.tensorPow (m + n), ⊤))

end F6ea14e94
end
end P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
