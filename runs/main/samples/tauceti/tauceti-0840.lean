public section

open Polynomial

namespace TauCeti

section BaseChange

variable {n : ℕ} {F : Type*} [Field F]
  {K : Type*} [Field K] [Algebra F K] [FiniteDimensional F K]

theorem irreducible_cyclotomic_of_coprime_finrank
    (hirr : Irreducible (cyclotomic n F))
    (hcop : n.totient.Coprime (Module.finrank F K)) :
    Irreducible (cyclotomic n K) := by
  -- Adjoin a root `α` of `Φ_n` to `F` and to `K` inside an algebraic closure of `K`.
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (cyclotomic n F)
    (degree_pos_of_irreducible hirr).ne'
  have hαK : aeval α (cyclotomic n K) = 0 := by
    rwa [← map_cyclotomic n (algebraMap F K), aeval_map_algebraMap]
  have hintF : IsIntegral F α := ⟨_, cyclotomic.monic n F, hα⟩
  have hintK : IsIntegral K α := ⟨_, cyclotomic.monic n K, hαK⟩
  let M := IntermediateField.adjoin F ({α} : Set (AlgebraicClosure K))
  let L := IntermediateField.adjoin K ({α} : Set (AlgebraicClosure K))
  have hMfin : Module.finrank F M = n.totient := by
    rw [IntermediateField.adjoin.finrank hintF,
      ← minpoly.eq_of_irreducible_of_monic hirr hα (cyclotomic.monic n F), natDegree_cyclotomic]
  -- `F(α)` has degree `φ(n)`, coprime to `[K : F]`, so it is linearly disjoint from `K` and
  -- `K(α)` still has degree `φ(n)` over `K`.
  have hdis : M.LinearDisjoint K :=
    IntermediateField.LinearDisjoint.of_finrank_coprime (hMfin ▸ hcop)
  have hMle : M ≤ L.restrictScalars F := by
    dsimp only [M, L]
    rw [IntermediateField.adjoin_le_iff]
    exact fun _ hx ↦ IntermediateField.subset_adjoin K _ hx
  have hadj : IntermediateField.adjoin K (M : Set (AlgebraicClosure K)) = L := by
    dsimp only [L]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact fun x hx ↦ hMle hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      apply IntermediateField.subset_adjoin K (M : Set (AlgebraicClosure K))
      dsimp only [M]
      exact IntermediateField.subset_adjoin F _ (Set.mem_singleton x)
  have : FiniteDimensional F M := IntermediateField.adjoin.finiteDimensional hintF
  have hrank := hdis.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hintK
  rw [hadj, ← Module.finrank_eq_rank' K L, ← Module.finrank_eq_rank' F M] at hrank
  have hLfin : Module.finrank K L = n.totient := by
    rw [← hMfin]
    exact_mod_cast hrank
  -- Hence the minimal polynomial of `α` over `K` is a monic factor of `Φ_n` of full degree.
  have hdeg : (cyclotomic n K).natDegree ≤ (minpoly K α).natDegree := by
    rw [natDegree_cyclotomic, ← hLfin, IntermediateField.adjoin.finrank hintK]
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintK) (cyclotomic.monic n K)
    (minpoly.dvd K α hαK) hdeg]
  exact minpoly.irreducible hintK

end BaseChange
end TauCeti
end
