@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.EquivalenceRelation

universe v u

variable {C : Type u} [Category.{v, u} C]
  {R X : C} {p₁ p₂ : R ⟶ X}

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport an internal equivalence relation across isomorphisms of its
relation object and object. -/
def transport (h : CategoryTheory.EquivalenceRelation p₁ p₂)
    {R' X' : C} (iR : R' ≅ R) (iX : X ≅ X') :
    CategoryTheory.EquivalenceRelation
      (iR.hom ≫ p₁ ≫ iX.hom) (iR.hom ≫ p₂ ≫ iX.hom) := by
  let c : PullbackCone
      (iR.hom ≫ p₂ ≫ iX.hom) (iR.hom ≫ p₁ ≫ iX.hom) :=
    PullbackCone.mk (h.c.fst ≫ iR.inv) (h.c.snd ≫ iR.inv) (by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun k ↦ k ≫ iX.hom) h.c.condition)
  have hc : IsLimit c := by
    let hp : IsPullback h.c.fst h.c.snd p₂ p₁ :=
      IsPullback.of_isLimit h.isLimit
    have hp' : IsPullback (h.c.fst ≫ iR.inv) (h.c.snd ≫ iR.inv)
        (iR.hom ≫ p₂ ≫ iX.hom) (iR.hom ≫ p₁ ≫ iX.hom) := by
      apply hp.of_iso (Iso.refl _) iR.symm iR.symm iX
      all_goals simp
    exact hp'.isLimit
  have c_fst : c.fst = h.c.fst ≫ iR.inv := rfl
  have c_snd : c.snd = h.c.snd ≫ iR.inv := rfl
  refine
    { right_cancellation := ?_
      r := iX.inv ≫ h.r ≫ iR.inv
      reflexivity₁ := by simp
      reflexivity₂ := by simp
      s := iR.hom ≫ h.s ≫ iR.inv
      symmetry₁ := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc,
          Iso.cancel_iso_hom_left]
        exact h.symmetry₁_assoc iX.hom
      symmetry₂ := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc,
          Iso.cancel_iso_hom_left]
        exact h.symmetry₂_assoc iX.hom
      c := c
      isLimit := hc
      t := h.t ≫ iR.inv
      transitivity₁ := ?_
      transitivity₂ := ?_ }
  · intro Y f g h₁ h₂
    rw [← cancel_mono iR.hom]
    apply h.toJointlyMono₂.right_cancellation
    · rw [← cancel_mono iX.hom]
      simpa only [Category.assoc] using h₁
    · rw [← cancel_mono iX.hom]
      simpa only [Category.assoc] using h₂
  · rw [c_fst]
    calc
      (h.t ≫ iR.inv) ≫ (iR.hom ≫ p₁ ≫ iX.hom) =
          h.t ≫ p₁ ≫ iX.hom := by simp
      _ = h.c.fst ≫ p₁ ≫ iX.hom := h.transitivity₁_assoc iX.hom
      _ = (h.c.fst ≫ iR.inv) ≫
          (iR.hom ≫ p₁ ≫ iX.hom) := by simp
  · rw [c_snd]
    calc
      (h.t ≫ iR.inv) ≫ (iR.hom ≫ p₂ ≫ iX.hom) =
          h.t ≫ p₂ ≫ iX.hom := by simp
      _ = h.c.snd ≫ p₂ ≫ iX.hom := h.transitivity₂_assoc iX.hom
      _ = (h.c.snd ≫ iR.inv) ≫
          (iR.hom ≫ p₂ ≫ iX.hom) := by simp

end CategoryTheory.EquivalenceRelation
end
end
