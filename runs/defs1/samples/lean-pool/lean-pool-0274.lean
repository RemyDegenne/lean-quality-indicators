@[expose] public section

open MvPolynomial

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

noncomputable section AristotleLemmas

/-- The transformation T maps a sequence `b` to `b'` by finding the largest index
`j` such that `b_j > k + 1 - j` and setting `b'_j = b_j - 1`. If no such `j`
exists (i.e. `b` is the base sequence), it returns `b`. -/
noncomputable def transformSeq (k : ℕ) (b : Fin (k + 1) → ℕ) : Fin (k + 1) → ℕ :=
  let s := (Finset.univ : Finset (Fin (k + 1))).filter (fun j => baseSeq k j < b j)
  if h : s.Nonempty then
    let j := s.max' h
    Function.update b j (b j - 1)
  else
    b

end AristotleLemmas
end
