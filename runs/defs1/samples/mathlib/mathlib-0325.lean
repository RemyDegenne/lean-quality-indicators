@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

variable (I : IdealSheafData X)

section ofIsClosed

open _root_.PrimeSpectrum TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- The vanishing ideal sheaf of a closed set,
which is the largest ideal sheaf whose support is equal to it.
The reduced induced scheme structure on the closed set is the quotient of this ideal. -/
@[simps! ideal coe_support]
noncomputable nonrec def vanishingIdeal (Z : Closeds X) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ vanishingIdeal (U.2.fromSpec ⁻¹' Z))
    (fun U f ↦ by
      let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        suffices ∀ p, (X.affineBasicOpen f).2.fromSpec p ∈ Z → F.hom x ∈ p.asIdeal by
          simpa [PrimeSpectrum.mem_vanishingIdeal] using! this
        intro x hxZ
        refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx
          (Spec.map (X.presheaf.map (homOfLE _).op) x) ?_
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply,
          IsAffineOpen.map_fromSpec _ (X.affineBasicOpen f).2]
      · let : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) := F.hom.toAlgebra
        have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
          U.2.isLocalization_of_eq_basicOpen _ _ rfl
        intro x hx
        dsimp only at hx ⊢
        have : Topology.IsOpenEmbedding (Spec.map F) :=
          localization_away_isOpenEmbedding Γ(X, X.basicOpen f) f
        rw [← U.2.map_fromSpec (X.affineBasicOpen f).2 (homOfLE (X.basicOpen_le f)).op,
          Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hx
        generalize U.2.fromSpec ⁻¹' Z = Z' at hx ⊢
        replace hx : x ∈ vanishingIdeal (Spec.map F ⁻¹' Z') := hx
        obtain ⟨I, hI, e⟩ :=
          (isClosed_iff_zeroLocus_radical_ideal _).mp (isClosed_closure (s := Z'))
        rw [← vanishingIdeal_closure,
          ← this.isOpenMap.preimage_closure_eq_closure_preimage this.continuous, e] at hx
        rw [← vanishingIdeal_closure, e]
        erw [preimage_comap_zeroLocus] at hx
        rwa [← PrimeSpectrum.zeroLocus_span, ← Ideal.map, vanishingIdeal_zeroLocus_eq_radical,
          ← RingHom.algebraMap_toAlgebra (X.presheaf.map _).hom,
          ← IsLocalization.map_radical (.powers f), ← vanishingIdeal_zeroLocus_eq_radical] at hx)
    Z
    (fun U x hxU ↦ by
      trans x ∈ X.zeroLocus (U := U.1) (vanishingIdeal (U.2.fromSpec ⁻¹' Z)) ∩ U.1
      · rw [← U.2.fromSpec_image_zeroLocus, zeroLocus_vanishingIdeal_eq_closure,
          ← U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
            U.2.fromSpec.continuous,
          Set.image_preimage_eq_inter_range, Z.isClosed.closure_eq, IsAffineOpen.range_fromSpec]
        simp [hxU]
      · simp [hxU])

end ofIsClosed
end IdealSheafData
end AlgebraicGeometry.Scheme
end
