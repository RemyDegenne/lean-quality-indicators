@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem locallyQuasiFinite_of_finite_geometric_point_fibers [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (g : Spec (CommRingCat.of K) ⟶ Y),
      Set.Finite {q : Spec (CommRingCat.of K) ⟶ X | q ≫ f = g}) :
    LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton f
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  let g : Spec (CommRingCat.of K) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
      Y.fromSpecResidueField y
  let P : Scheme.{u} := Limits.pullback f g
  have : Finite {q : Spec (CommRingCat.of K) ⟶ X // q ≫ f = g} := h K g
  -- A section of the geometric fiber is determined by its first projection.
  have : Finite {q : Spec (CommRingCat.of K) ⟶ P //
      q ≫ Limits.pullback.snd f g = 𝟙 _} := by
    refine Finite.of_injective
      (fun q ↦ (⟨q.1 ≫ Limits.pullback.fst f g, ?_⟩ :
        {q : Spec (CommRingCat.of K) ⟶ X // q ≫ f = g})) ?_
    · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
        q.2, Category.id_comp]
    · intro q₁ q₂ e
      apply Subtype.ext
      apply Limits.pullback.hom_ext
      · exact congrArg Subtype.val e
      · exact q₁.2.trans q₂.2.symm
  have hclosed : (closedPoints P).Finite :=
    Finite.of_surjective (pointEquivClosedPoint (Limits.pullback.snd f g))
      (pointEquivClosedPoint (Limits.pullback.snd f g)).surjective
  let : JacobsonSpace P :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd f g)
  let : DiscreteTopology P := JacobsonSpace.discreteTopology hclosed
  let : Finite P := Set.finite_univ_iff.mp (by
    simpa only [closedPoints_eq_univ] using hclosed)
  have hg : Set.range g = {y} := Set.range_eq_singleton fun x ↦ by
    simp only [g, Scheme.Hom.comp_apply]
    exact Y.fromSpecResidueField_apply y _
  simpa only [Set.image_univ, Scheme.Pullback.range_fst, hg] using
    (Set.finite_univ (α := P)).image (Limits.pullback.fst f g)

end AlgebraicGeometry.Scheme.Hom
end
