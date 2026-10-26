import Mathlib
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite

set_option autoImplicit false

universe u

open CategoryTheory hiding IsDiscrete
p2m_open "CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry"

namespace QFPtDesc

theorem sfq {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map (q.residueFieldMap x)) := by
  refine ⟨⟨⟨fun z => ⟨default, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  letI := (q.residueFieldMap x).hom.toAlgebra
  show Module.Flat (Y.residueField (q x)) (X.residueField x)
  infer_instance

theorem locallyQuasiFinite_fiberToSpecResidueField
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyQuasiFinite f'] (y' : Y') :
    LocallyQuasiFinite (f.fiberToSpecResidueField (q y')) := by
  haveI := AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have sq' := isPullback_fiberToSpecResidueField_of_isPullback sq y'
  have hf' : LocallyQuasiFinite (f'.fiberToSpecResidueField y') :=
    MorphismProperty.pullback_snd (P := @LocallyQuasiFinite) f' (Y'.fromSpecResidueField y') inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyQuasiFinite)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq'.flip (sfq q y') hf'

theorem main
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]

  have hlqf : LocallyQuasiFinite (f.fiberToSpecResidueField (f x)) := by
    rw [hx]; exact locallyQuasiFinite_fiberToSpecResidueField sq y'
  have hdisc : _root_.IsDiscrete ((f.fiberToSpecResidueField (f x)) ⁻¹'
      {(f.fiberToSpecResidueField (f x)) (f.asFiber x)}) :=
    (f.fiberToSpecResidueField (f x)).isDiscrete_preimage_singleton _
  have huniv : ((f.fiberToSpecResidueField (f x)) ⁻¹'
      {(f.fiberToSpecResidueField (f x)) (f.asFiber x)}) = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv, isDiscrete_univ_iff] at hdisc
  exact isOpen_discrete _

end QFPtDesc

theorem solution
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x :=
  QFPtDesc.main sq y' x hx
