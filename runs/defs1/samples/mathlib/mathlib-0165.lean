@[expose] public section

variable {p : ℕ} {K : Type*}

namespace FirstOrder

namespace Field

open Language FirstOrder.Ring

/-- For a given natural number `n`, `eqZero n` is the sentence in the language of rings
saying that `n` is zero. -/
noncomputable def eqZero (n : ℕ) : Language.ring.Sentence :=
  Term.equal (termOfFreeCommRing n) 0

end Field
end FirstOrder
end
