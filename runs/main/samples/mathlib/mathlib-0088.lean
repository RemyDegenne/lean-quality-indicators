@[expose] public section

variable {M : Type*}

section Monoid

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

@[to_additive (attr := simp)]
lemma Units.pow_ofPowEqOne (ha : a ^ n = 1) (hn : n ≠ 0) :
    Units.ofPowEqOne _ n ha hn ^ n = 1 := Units.ext <| by simp [ha]

end Monoid
end
