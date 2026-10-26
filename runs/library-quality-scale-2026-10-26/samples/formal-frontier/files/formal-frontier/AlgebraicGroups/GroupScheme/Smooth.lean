/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
The Mathlib notice above applies to the adapted identity-point smoothness proof.
Modifications by Formal Frontier Agents: adapt the closed-point translation and
algebraic-closure descent of Mathlib's `AlgebraicGeometry.smooth_of_grpObj`.
-/
module

public import AlgebraicGroups.GroupObject.BaseChange
public import AlgebraicGroups.GroupObject.KernelTorsor
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Smooth morphisms of group schemes

This file proves that a group scheme locally of finite type over an algebraically closed field is
smooth when its identity point is smooth. It also derives smoothness of a faithfully flat, locally
finitely presented morphism of group schemes from smoothness of its kernel.

## References

- J. S. Milne, *Algebraic Groups*, Proposition 1.28, for propagation of
  smoothness from the identity point in an algebraic group; Propositions
  1.62(a) and 8.1(a) for smoothness of a group extension with smooth
  kernel and quotient. These results concern algebraic groups over fields.
- Mathlib's `AlgebraicGeometry.smooth_of_grpObj` and its algebraically closed helper in
  `Mathlib.AlgebraicGeometry.Group.Smooth` provide the adapted closed-point translation
  and algebraic-closure descent proof. Mathlib assumes geometric reducedness for the group
  scheme; the identity-point result here assumes smoothness at the identity instead.
- Mathlib's `GrpObj.mulRight`, `Scheme.Hom.smoothLocus`,
  `MorphismProperty.of_pullback_snd_of_descendsAlong`, and smooth descent
  provide the point-translation, base-change, and descent APIs. The
  kernel-torsor pullback identifies the self-pullback of the quotient with a
  base change of the kernel; this is a different route from Milne's fibrewise
  argument.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Category

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A group scheme locally of finite type over an algebraically closed field is smooth if its
identity point belongs to the smooth locus. This is the algebraically closed case of
Milne, *Algebraic Groups*, Proposition 1.28. Its closed-point translation adapts Mathlib's
algebraically closed helper for `AlgebraicGeometry.smooth_of_grpObj`, assuming smoothness at
the identity rather than reducedness. -/
theorem smooth_of_unit_mem_smoothLocus_of_isAlgClosed
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)]
    (h : η[Over.mk f].left (IsLocalRing.closedPoint K) ∈ f.smoothLocus) : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := η[Over.mk f]
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  let β : X ≅ X := (Over.forget _).mapIso α
  have hβ : β.hom x = η[Over.mk f].left (IsLocalRing.closedPoint K) := by
    have hx' : x'.left (IsLocalRing.closedPoint K) = x := by
      change pointOfClosedPoint f x _ (IsLocalRing.closedPoint K) = x
      exact pointOfClosedPoint_apply f x _ _
    rw [← hx']
    exact congr(($hα).left (IsLocalRing.closedPoint K))
  rw! [← hβ, ← β.hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show β.hom ≫ f = f from α.hom.w] at h
  exact hx h

private lemma exists_open_smooth_neighborhood (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] (x : X) (h : x ∈ f.smoothLocus) :
    ∃ (V : X.Opens), x ∈ V ∧ Smooth (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hVU, hx, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f x h
  refine ⟨V, hx, ?_⟩
  let _ : IsAffine (U : Scheme) := hU
  let _ : IsAffine (V : Scheme) := hV
  have hres : Smooth (f.resLE U V hVU) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U V hVU)).mpr H
  rw [← Scheme.Hom.resLE_comp_ι f hVU]
  exact MorphismProperty.comp_mem (@Smooth) _ _ hres inferInstance

/-- A group scheme locally of finite type over a field is smooth if its identity point belongs to
the smooth locus, the identity-point implication in Milne, *Algebraic Groups*,
Proposition 1.28. The proof follows the algebraic-closure descent of Mathlib's
`AlgebraicGeometry.smooth_of_grpObj`, replacing its geometric-reducedness input with
smoothness at the identity; it does not assert that regularity of the identity stalk
implies smoothness. -/
theorem smooth_of_unit_mem_smoothLocus
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [GrpObj (Over.mk f)]
    (h : η[Over.mk f].left (IsLocalRing.closedPoint K) ∈ f.smoothLocus) : Smooth f := by
  let Ω : Type u := AlgebraicClosure K
  let g : Spec (.of Ω) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom <| algebraMap K Ω)
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · let fΩ : pullback f g ⟶ Spec (.of Ω) := pullback.snd f g
    let _ : GrpObj (Over.mk fΩ) := Over.grpObjMkPullbackSnd
    apply smooth_of_unit_mem_smoothLocus_of_isAlgClosed fΩ
    obtain ⟨V, hηV, hVf⟩ := exists_open_smooth_neighborhood f _ h
    have hηrange : Set.range (g ≫ η[Over.mk f].left) ⊆ Set.range V.ι := by
      rintro _ ⟨y, rfl⟩
      refine ⟨⟨(g ≫ η[Over.mk f].left) y, ?_⟩, rfl⟩
      rw [Scheme.Hom.comp_apply]
      simpa only [Subsingleton.elim (g y) (IsLocalRing.closedPoint K)] using hηV
    let e : Spec (.of Ω) ⟶ V :=
      IsOpenImmersion.lift V.ι (g ≫ η[Over.mk f].left) hηrange
    have he : e ≫ V.ι = g ≫ η[Over.mk f].left :=
      IsOpenImmersion.lift_fac _ _ _
    have hunit : η[Over.mk f].left ≫ f = 𝟙 _ := by
      simpa using η[Over.mk f].w
    let m : pullback (V.ι ≫ f) g ⟶ pullback f g :=
      pullback.map (V.ι ≫ f) g f g V.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
    let eW : Spec (.of Ω) ⟶ pullback (V.ι ≫ f) g :=
      pullback.lift e (𝟙 _) (by
        rw [← Category.assoc, he, Category.assoc, hunit]
        simp)
    have hm : eW ≫ m = η[Over.mk fΩ].left := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        simp only [m, eW, pullback.lift_fst]
        rw [← Category.assoc, pullback.lift_fst, he]
        exact (Over.unit_pullback_fst f g).symm
      · rw [Category.assoc]
        simp only [m, eW, pullback.lift_snd]
        rw [← Category.assoc, pullback.lift_snd]
        simpa [fΩ] using η[Over.mk fΩ].w.symm
    have hW : Smooth (m ≫ fΩ) := by
      have : Smooth (pullback.snd (V.ι ≫ f) g) :=
        smooth_isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback (V.ι ≫ f) g) hVf
      have hm_snd : m ≫ fΩ = pullback.snd (V.ι ≫ f) g := by
        dsimp only [m, fΩ, pullback.map]
        rw [pullback.lift_snd]
        simp
      rw [hm_snd]
      exact this
    have hmem : eW (IsLocalRing.closedPoint Ω) ∈ (m ≫ fΩ).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top (m ≫ fΩ)]
      trivial
    rw [← Scheme.Hom.preimage_smoothLocus_eq m fΩ,
      Scheme.Hom.mem_preimage] at hmem
    rw [← congr(($hm) (IsLocalRing.closedPoint Ω))]
    exact hmem

private lemma smooth_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@Smooth.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  let P : MorphismProperty Scheme.{u} := @Smooth.{u}
  let hlocal : IsZariskiLocalAtTarget P :=
    HasRingHomProperty.instIsZariskiLocalAtTarget P (Q := RingHom.Smooth)
  let hfpqc : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    inferInstance
  exact inferInstanceAs
    (P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation))

variable {S : Scheme.{u}} {N G Q : Over S} [GrpObj G] [GrpObj Q]

/-- A faithfully flat, locally finitely presented morphism of group schemes with smooth kernel is
smooth. The kernel is expressed by a pullback square over the unit section. This strengthens the
field-group smooth-extension argument of Milne, *Algebraic Groups*, Proposition 1.62(a):
the base may be any scheme, and the quotient need not itself be smooth for this conclusion.
The proof descends smoothness along the quotient via the kernel-torsor square. -/
theorem smooth_of_smooth_kernel (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q])
    [Smooth N.hom] [Surjective q.left] [Flat q.left]
    [LocallyOfFinitePresentation q.left] : Smooth q.left := by
  apply smooth_descendsAlong_fppf.of_isPullback
    ((CategoryTheory.GrpObj.isPullback_kernel_mul i q hN).map (Over.forget S)).flip
  · rw [Over.forget_map]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · change Smooth (pullback.snd N.hom G.hom)
    exact smooth_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback N.hom G.hom)
      (show Smooth N.hom from inferInstance)

/-- In a faithfully flat, locally finitely presented extension of group schemes, a smooth kernel
and smooth quotient imply that the middle group scheme is smooth. This extends Milne,
*Algebraic Groups*, Propositions 1.62(a) and 8.1(a) from algebraic groups over fields
to group schemes over arbitrary bases; flatness, surjectivity, a locally finitely presented
quotient map, and the kernel pullback square remain hypotheses. -/
theorem smooth_of_smooth_kernel_quotient (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q])
    [Smooth N.hom] [Surjective q.left] [Flat q.left]
    [LocallyOfFinitePresentation q.left] [Smooth Q.hom] : Smooth G.hom := by
  rw [← q.w]
  exact MorphismProperty.comp_mem (@Smooth) q.left Q.hom
    (smooth_of_smooth_kernel i q hN) inferInstance

end AlgebraicGeometry
