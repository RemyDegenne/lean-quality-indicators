namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away

set_option autoImplicit false

set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

namespace GlobalPresLocal

p2m_open

section Transfer

variable {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] (r : S) [IsLocalization.Away r B]
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of S)) (f' : X' ⟶ Spec (.of B)) (p : X' ⟶ X) [IsOpenImmersion p]
  (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
  (M : X.Modules)

variable {N' : ℕ}
  (𝔓 : ((Scheme.Modules.pullback p).obj M).ProjPresentation f' N')

include hp in

theorem exists_t (i : Fin (N' + 1)) :
    ∃ t : Γ(M, Ug r f), pull p M (Ug r f) t
      = ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ Ug r f ≤ ⊤)).op (𝔓.σ i) :=
  (pull_bijective p M (Ug r f) (opensRange_p r f f' p hp).ge).2 _

end Transfer
end GlobalPresLocal
end Modules
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away
