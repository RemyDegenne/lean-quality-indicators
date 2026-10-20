namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial

attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx

set_option autoImplicit false

universe u

noncomputable section

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

namespace SesAffine

p2m_open

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

end SesAffine
end Modules
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
