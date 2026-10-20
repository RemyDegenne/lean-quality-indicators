public section

namespace TauCeti

universe u v

variable {p : ℕ} [hp : Fact p.Prime]

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]

theorem exists_notMem_nsmul_mem_smul_sub_mem_of_isProP (hG : IsProP p G)
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) {N : AddSubgroup M}
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (hN' : N ≠ ⊤) :
    ∃ x : M, x ∉ N ∧ p • x ∈ N ∧ ∀ g : G, g • x - x ∈ N := by
  let _ := N.quotientDistribMulAction hN
  -- the stabilizer of a class is the preimage of the open set `N`, so the kernel is open
  have hK : IsOpen ((MulAction.toPermHom G (M ⧸ N)).ker : Set G) := by
    rw [ker_toPermHom_eq_iInf_stabilizer, Subgroup.coe_iInf]
    refine isOpen_iInter_of_finite fun y ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    have : (MulAction.stabilizer G (x : M ⧸ N) : Set G) = (fun g : G ↦ g • x - x) ⁻¹' N := by
      ext g
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage,
        AddSubgroup.quotientDistribMulAction_smul_mk, QuotientAddGroup.eq_iff_sub_mem]
    rw [this]
    exact (isOpen_discrete _).preimage
      ((continuous_of_discreteTopology (f := fun m : M ↦ m - x)).comp
        (continuous_id.smul continuous_const))
  have : Nontrivial (M ⧸ N) := QuotientAddGroup.nontrivial_iff.mpr hN'
  have htors' : ∀ y : M ⧸ N, ∃ k : ℕ, p ^ k • y = 0 := fun y ↦ by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨k, hk⟩ := htors x
    exact ⟨k, by rw [← QuotientAddGroup.mk_nsmul, hk, QuotientAddGroup.mk_zero]⟩
  obtain ⟨y, hy0, hpy, hy⟩ :=
    exists_ne_zero_nsmul_eq_zero_invariant_of_isProP_of_isOpen_ker hG hK htors'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨x, fun hx ↦ hy0 ((QuotientAddGroup.eq_zero_iff x).mpr hx), ?_, fun g ↦ ?_⟩
  · rwa [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hpy
  · have := hy g
    rwa [AddSubgroup.quotientDistribMulAction_smul_mk, QuotientAddGroup.eq_iff_sub_mem] at this

end Quotient
end TauCeti
end
