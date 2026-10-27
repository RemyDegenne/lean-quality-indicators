@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation.Restrict

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

/-- Restriction to an invariant open preserves an internal scheme equivalence
relation. This generalizes the invariant constant-rank-open restriction used
in Stacks Project, Lemma 39.23.3 (tag 03BI): equality of the two leg
preimages suffices, without any rank, finiteness, flatness or quotient
assumption. -/
def equivalenceRelation (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    EquivalenceRelation (p₁ ∣_ U) (snd U hU) where
  right_cancellation Y f g hfst hsnd := by
    rw [← cancel_mono (p₁ ⁻¹ᵁ U).ι]
    apply h.toJointlyMono₂.right_cancellation
    · simpa only [Category.assoc, ← morphismRestrict_ι] using
        congrArg (fun k => k ≫ U.ι) hfst
    · simpa only [Category.assoc, ← snd_ι U hU] using
        congrArg (fun k => k ≫ U.ι) hsnd
  r := reflexivity h U
  reflexivity₁ := reflexivity_fst h U
  reflexivity₂ := reflexivity_snd h U hU
  s := symmetry h U hU
  symmetry₁ := symmetry_fst h U hU
  symmetry₂ := symmetry_snd h U hU
  c := compositionCone U hU
  isLimit := by
    simpa only [compositionCone] using
      (pullbackIsPullback (snd U hU) (p₁ ∣_ U))
  t := transitivity h U hU
  transitivity₁ := transitivity_fst h U hU
  transitivity₂ := transitivity_snd h U hU

end AlgebraicGeometry.EquivalenceRelation.Restrict
end
end
