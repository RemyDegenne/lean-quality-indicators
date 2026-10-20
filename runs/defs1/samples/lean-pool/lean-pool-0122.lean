@[expose] public section

universe u v

/-- Sauer-Shelah via Mathlib: |C|_S| ≤ Σ_{i ≤ d} C(|S|, i).
    The proof chain:
    1. Convert C|_S to a Finset family over S (conceptToFinset on restrictions)
    2. Apply card_le_card_shatterer: |𝒜| ≤ |𝒜.shatterer|
    3. Apply card_shatterer_le_sum_vcDim: |𝒜.shatterer| ≤ Σ C(|S|, i) for i ≤ vcDim(𝒜)
    4. Show vcDim(𝒜) ≤ d (restriction doesn't increase VCDim)
    This requires building the S-local Finset family from C|_S. -/
-- Convert Finset (↥S → Bool) to Finset (Finset ↥S). Each f maps to {x | f x = true}.
def funcToSubsetFamily {X : Type u} [DecidableEq X] (S : Finset X)
    (fs : Finset (↥S → Bool)) : Finset (Finset ↥S) :=
  fs.image (fun f => Finset.univ.filter (fun x => f x = true))

end
