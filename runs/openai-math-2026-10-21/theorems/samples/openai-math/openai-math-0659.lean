namespace OAI

open Erdos970

noncomputable section

open scoped BigOperators

namespace Ostmann.Characters.DiagonalEstimate

open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate

open InitialCharacterScale

attribute [local instance] Classical.propDecidable

section

variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

theorem sourceHistoryPairMean_eq_zero_of_not_preserves_bulk
    (P : ℕ+) (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (he : ¬∀i,IsCopiedBulk w.configuration (wordSize k L) j (e i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i) :
    sourceHistoryPairMean w j hj B V P e h h'=0 := by
  have hw : 0 < s.locations.w := by
    linarith [s.locations.small_start,s.locations.small_end]
  have hsource : (fun i=>sourceScheduledShells w j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)) =
      actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes := rfl
  unfold sourceHistoryPairMean FinitePrior.cmean
  apply Finset.sum_eq_zero
  intro y hy
  apply mul_eq_zero_of_right
  apply normalizedHistoryPair_eq_zero_of_unsupported_matching
  intro f hf hs
  apply he
  intro i
  have hfi := primeProductPrior_mem_of_mass_ne_zero _
    (fun _=>sourceScheduledShells_pos w j _) f hf (e i)
  have hsi := hs i
  have hfis := (congrArg (fun A=>f (e i)∈A) (congrFun hsource (e i))).mp hfi
  have hsis := (congrArg (fun A=>f (e i)∈A) (congrFun hsource i)).mp hsi
  exact (actualCopied_mem_bulk_iff w hw j (e i) (f (e i)) hfis).symm.trans
    (actualCopied_mem_bulk_iff w hw j i (f (e i)) hsis)

end
end Ostmann.Characters.DiagonalEstimate
end
end OAI
