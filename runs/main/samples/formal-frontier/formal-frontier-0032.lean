@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

theorem ext_of_fromSpecResidueField
    {X Y : Scheme.{u}} [IsReduced X] {f g : X ⟶ Y}
    (h : ∀ x : X, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g) :
    f = g := by
  have hpoint (x : X) : f x = g x := by
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
      congrArg (fun k : Spec (X.residueField x) ⟶ Y => k default) (h x)
  apply Scheme.hom_ext_of_forall f g
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  let U : X.Opens := (f ⁻¹ᵁ V) ⊓ (g ⁻¹ᵁ V)
  have hxU : x ∈ U := ⟨hxV, by
    change g x ∈ V
    rw [← hpoint x]
    exact hxV⟩
  let : IsAffine V := hV
  have hf : U ≤ f ⁻¹ᵁ V := inf_le_left
  have hg : U ≤ g ⁻¹ᵁ V := inf_le_right
  let fU : U.toScheme ⟶ V.toScheme := f.resLE V U hf
  let gU : U.toScheme ⟶ V.toScheme := g.resLE V U hg
  have hres (z : U.toScheme) :
      U.toScheme.fromSpecResidueField z ≫ fU =
        U.toScheme.fromSpecResidueField z ≫ gU := by
    apply (cancel_mono V.ι).1
    simpa only [Category.assoc, fU, gU, resLE_comp_ι,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc] using
      congrArg (fun k => Spec.map ((U.ι).residueFieldMap z) ≫ k) (h (U.ι z))
  have hfg : fU = gU := by
    apply AlgebraicGeometry.ext_of_fromSpecResidueField_eq fU gU
      (CategoryTheory.Limits.terminal.from V.toScheme) Set.univ dense_univ
    · intro z _
      exact hres z
    · exact CategoryTheory.Limits.terminal.hom_ext _ _
  refine ⟨U, hxU, ?_⟩
  simpa only [fU, gU, resLE_comp_ι] using
    congrArg (fun k : U.toScheme ⟶ V.toScheme => k ≫ V.ι) hfg

end AlgebraicGeometry.Scheme.Hom
end
