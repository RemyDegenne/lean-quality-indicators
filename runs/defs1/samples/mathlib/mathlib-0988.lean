@[expose] public section

open Set

variable {ι : Sort*} {α : Type*} (s : Set α)

section OrdConnected

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
noncomputable abbrev subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    isLUB_csSup t ht h_bdd := .of_image Subtype.coe_le_coe <| by
      rw [← subset_sSup_of_within s ht h_bdd (h_Sup ht h_bdd)]
      exact isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd)
    isGLB_csInf t ht h_bdd := .of_image Subtype.coe_le_coe <| by
      rw [← subset_sInf_of_within s ht h_bdd (h_Inf ht h_bdd)]
      exact isGLB_csInf (ht.image _) ((Subtype.mono_coe _).map_bddBelow h_bdd)
    csSup_of_not_bddAbove := fun t ht ↦ by simp [ht]
    csInf_of_not_bddBelow := fun t ht ↦ by simp [ht] }

end OrdConnected
end
