namespace P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away

set_option autoImplicit false

p2m_open

namespace GrassBridgeH1

p2m_reactivate

scoped instance isCoverDense_Spec : Scheme.Spec.IsCoverDense Scheme.zariskiTopology.{0} where
  is_cover X := by
    rw [Scheme.mem_grothendieckTopology_iff]
    refine ⟨X.affineCover, ?_⟩
    rintro Y f ⟨i⟩
    exact ⟨{obj := op _, lift := 𝟙 _, map := X.affineCover.f i, fac := Category.id_comp _}⟩

scoped instance isOneHypercoverDense_Spec :
    Functor.IsOneHypercoverDense.{0} Scheme.Spec J₀ Scheme.zariskiTopology.{0} :=
  Functor.IsOneHypercoverDense.of_hasPullbacks fun X =>
    ⟨X.affineCover.I₀, fun i => op (X.local_affine i).choose_spec.choose, X.affineCover.f,
      X.affineCover.mem_grothendieckTopology⟩

p2m_reactivate

namespace Datum

variable {R : Type} [CommRing R] (D : Datum R) (hD : D.IsSheaf)

section ev

variable (A : Type) [CommRing A] [instA : Algebra R A]

noncomputable def germ (z : (D.G hD).obj (op (ovr A))) : D.Tot (CommRingCat.of A) :=
  D.aff hD (z.1 : (D.H hD).obj (op (Spec (.of A)))) (𝟙 (Spec (.of A)))

end ev
end Datum
end GrassBridgeH1
end P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away
