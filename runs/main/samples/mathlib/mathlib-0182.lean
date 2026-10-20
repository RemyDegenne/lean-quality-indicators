@[expose] public noncomputable section

namespace UniqueFactorizationMonoid

variable {M : Type*} [CommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M] {a b u : M}

@[simp]
lemma radical_radical : radical (radical a) = radical a :=
  radical_eq_iff_primeFactors_eq.mpr primeFactors_radical

end UniqueFactorizationMonoid
end
