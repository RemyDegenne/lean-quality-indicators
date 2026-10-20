namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_kernelTrivial_of_locIsoOnBase

set_option autoImplicit false

open scoped TensorProduct

p2m_open

universe u v

noncomputable section

namespace T3G1Kit

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

include hom in

theorem root_transport (hP : IsPullback u f' f ψ) (M 𝓛₀ : A.Modules) (h0inv : Scheme.Modules.IsInvertible 𝓛₀)
    (h0ker : KernelTrivial f L 𝓛₀)
    (h0loc : LocIsoOnBase f M (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
        ((Scheme.Modules.pullback u).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛₀)) := by
  refine ⟨h0inv.pullback u, kernelTrivial_of_isPullback L L' ψ u hu hom hP 𝓛₀ h0inv h0ker, ?_⟩
  have H : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
      ((Scheme.Modules.pullback u).obj (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu h0loc
  refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans H (locIsoOnBase_of_iso f' ?_)
  exact Scheme.Modules.pullbackTensorObjIso u _ _ ≪≫
    whiskerLeftIso _
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛₀ ≪≫
        (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom).symm).app 𝓛₀ ≪≫
        ((Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛₀).symm)

end Hom
end T3G1Kit
end
end P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_kernelTrivial_of_locIsoOnBase
