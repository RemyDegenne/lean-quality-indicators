@[expose] public section

open Order

variable {α ι : Type*} [GeneralizedBooleanAlgebra α]

section Nat

/-- A recursion principle for `disjointed`. To construct / define something for `disjointed f i`,
it's enough to construct / define it for `f n` and to able to extend through diffs.

Note that this version allows an arbitrary `Sort*`, but requires the domain to be `Nat`, while
the root-level `disjointedRec` allows more general domains but requires `p` to be `Prop`-valued. -/
def Nat.disjointedRec {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃n⦄, p (f n) → p (disjointed f n)
  | 0 => fun h₀ ↦ disjointed_zero f ▸ h₀
  | n + 1 => fun h => by
    suffices H : ∀ k, p (f (n + 1) \ partialSups f k) from disjointed_add_one f n ▸ H n
    intro k
    induction k with
    | zero => exact hdiff h
    | succ k ih => simpa only [partialSups_add_one, ← sdiff_sdiff_left] using hdiff ih

end Nat
end
