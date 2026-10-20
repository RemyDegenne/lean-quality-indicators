@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

section SymPow

/-- **The symmetric power**: the coinvariants of the symmetriser's
action — the coequalizer of the action against the identity.  The
idempotency splits it off as a direct summand of the module power,
with section `symPowσ`; this presentation is chosen because the
consumers of the Key Lemma build morphisms out of the symmetric
power by descent along `symPowπ` and morphisms into it through the
section. -/
noncomputable def symPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : D :=
  coequalizer (symPowIdem A X n) (𝟙 (modPow A X n))

end SymPow
end RS
end
