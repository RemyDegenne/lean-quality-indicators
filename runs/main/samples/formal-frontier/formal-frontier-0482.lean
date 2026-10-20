public section

set_option warningAsError true

open Set Topology TopologicalSpace CategoryTheory

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

theorem exists_isIntegral_open_of_isDomain_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    [IsDomain (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIntegral U.toScheme := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let Y := X.affineCover.X i
  let f : Y ⟶ X := X.affineCover.f i
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  let : IsDomain (Y.presheaf.stalk y) :=
    (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
      (X.presheaf.stalk (f y))
  obtain ⟨V, hclosure, hV⟩ :=
    exists_open_with_closure_eq_of_mem_irreducibleComponents Y
      (irreducibleComponent_mem_irreducibleComponents y)
  have hyV : y ∈ V := hV y fun W hW hyW ↦
    eq_irreducibleComponents_of_mem_of_isDomain_stalk Y y hW
      (irreducibleComponent_mem_irreducibleComponents y) hyW mem_irreducibleComponent
  have hVirr : IsIrreducible (V : Set Y) := by
    apply isIrreducible_iff_closure.mp
    rw [hclosure]
    exact isIrreducible_irreducibleComponent
  let R : Y.Opens :=
    ⟨{z : Y | _root_.IsReduced (Y.presheaf.stalk z)}, isOpen_setOf_isReduced_stalk Y⟩
  let U : Y.Opens := V ⊓ R
  have hyU : y ∈ U := by
    refine ⟨hyV, ?_⟩
    change _root_.IsReduced (Y.presheaf.stalk y)
    infer_instance
  have hUirr : IsIrreducible (U : Set Y) :=
    ⟨⟨y, hyU⟩, hVirr.2.open_subset U.isOpen (fun _ hz ↦ hz.1)⟩
  let : IrreducibleSpace U.toScheme := isIrreducible_iff_irreducibleSpace.mp hUirr
  let : ∀ z : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk z) := fun z ↦ by
    let : _root_.IsReduced (Y.presheaf.stalk z.1) := z.2.2
    exact isReduced_of_injective (U.stalkIso z).hom.hom
      (U.stalkIso z).commRingCatIsoToRingEquiv.injective
  let : IsReduced U.toScheme := isReduced_of_isReduced_stalk U.toScheme
  let : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced U.toScheme
  let g : U.toScheme ⟶ X := U.ι ≫ f
  refine ⟨g.opensRange, ?_, IsIntegral.of_isIso g.isoOpensRange.hom⟩
  refine ⟨⟨y, hyU⟩, ?_⟩
  change (U.ι ≫ f) (⟨y, hyU⟩ : U.toScheme) = f y
  exact Scheme.Hom.comp_apply U.ι f ⟨y, hyU⟩

end AlgebraicGeometry
end
