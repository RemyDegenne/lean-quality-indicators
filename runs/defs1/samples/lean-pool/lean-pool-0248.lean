@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

namespace MixedLetters

variable {A : Type u}

/-- **The normalised inclusion of a colouring**: the colouring
inclusion, read off the `U`-power normal form of its word power. -/
noncomputable def nIn
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin n → K) :
    tensorPow A U (popCount (par ∘ c)) ⟶ tensorPow A M n :=
  (normIso U n (par ∘ c)).inv ≫ S.colourInto n c

end MixedLetters
end RS
end
