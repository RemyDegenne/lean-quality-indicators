namespace P2MW.S_Submodule_exists_forall_finiteAdeleEvalAt_eq

open scoped TensorProduct

open IsDedekindDomain NumberField

noncomputable section

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Coord

variable {K : Type*} [Ring K] [Algebra ℚ K]

variable (S : Type*) [CommRing S] [Algebra ℚ S]

theorem la_mem_closure_iff_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (R : Subring S)
    (t : K ⊗[ℚ] S) :
    t ∈ AddSubgroup.closure
        {x : K ⊗[ℚ] S | ∃ z ∈ Submodule.span ℤ (Set.range b), ∃ s : S, s ∈ R ∧ x = z ⊗ₜ[ℚ] s}
      ↔ ∀ i, la_coord S b i t ∈ R := by
  constructor
  · intro ht i
    have hle : AddSubgroup.closure
        {x : K ⊗[ℚ] S | ∃ z ∈ Submodule.span ℤ (Set.range b), ∃ s : S, s ∈ R ∧ x = z ⊗ₜ[ℚ] s}
        ≤ (R.toAddSubgroup).comap (la_coord S b i).toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨z, hz, s, hs, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      exact la_coord_tmul_mem S b R i hz hs
    exact hle ht
  · intro h
    rw [← la_sum_tmul_coord S b t]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    exact AddSubgroup.subset_closure
      ⟨b i, Submodule.subset_span (Set.mem_range_self i), la_coord S b i t, h i, rfl⟩

end Coord
end
end P2MW.S_Submodule_exists_forall_finiteAdeleEvalAt_eq
