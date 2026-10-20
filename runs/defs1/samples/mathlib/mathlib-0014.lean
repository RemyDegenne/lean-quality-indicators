@[expose] public section

universe u

variable {L : Type u} [CommRing L] [IsDomain L]

variable (n : ℕ) [NeZero n]

variable (L)

variable {L}

variable (L) in
/--
Suppose `L` is a domain containing all `pⁱ`-th primitive roots with `p` a (rational) prime.
If `g` is a ring automorphism of `L`, then `cyclotomicCharacter L p g` is the unique `j : ℤₚ` such
that `g(ζ) = ζ ^ (j mod pⁱ)` for all `pⁱ`-th roots of unity `ζ`.

Note: This is the trivial character when `L` does not contain all `pⁱ`-th primitive roots.
-/
noncomputable def cyclotomicCharacter (p : ℕ) [Fact p.Prime] :
    (L ≃+* L) →* ℤ_[p]ˣ := .toHomUnits
  { toFun g := cyclotomicCharacter.toFun p g
    map_one' := by
      by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
        simp [cyclotomicCharacter.toZModPow_toFun]
      · simp [cyclotomicCharacter.toFun, dite_eq_right H]
    map_mul' f g := by
      by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · have _ (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
        simp [cyclotomicCharacter.toZModPow_toFun]
      · simp [cyclotomicCharacter.toFun, dite_eq_right H] }

end
