@[expose] public section

universe w uI u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) (c : Cone D) (hc : IsLimit c)

attribute [instance] ExistsHomHomCompEqCompAux.h𝒰S ExistsHomHomCompEqCompAux.h𝒰X

section IsAffine

open TopologicalSpace in
include hc in
lemma Scheme.exists_isOpenCover_and_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    {J : Type*} (U : J → c.pt.Opens) (hU : IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    ∃ (i : I) (s : Finset J) (V : s → (D.obj i).Opens),
      IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  have := compactSpace_of_isLimit D c hc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _
    (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  have hU : IsOpenCover fun j : s ↦ U ↑j := by
    simpa only [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe, Opens.coe_top, Opens.iSup_mk,
      Opens.carrier_eq_coe, Opens.coe_mk, Set.iUnion_subtype]
  obtain ⟨i, V, hV, heq⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite _ _ hc _ hU (hU' ·)
  use i, s, V, hV

end IsAffine
end AlgebraicGeometry
end
