@[expose] public section

namespace Int

/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
def leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : { lb : ℤ // P lb ∧ ∀ z : ℤ, P z → lb ≤ z } :=
  have EX : ∃ n : ℕ, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : ℤ), Nat.find_spec EX, fun z h => by
    obtain ⟨n, rfl⟩ := le.dest (Hb _ h); grw [Nat.find_min' EX h]⟩

end Int
end
