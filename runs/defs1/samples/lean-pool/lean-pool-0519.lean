@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section Norm

variable {A : Type u}

/-- **The normalisation of a word power**: strip the unit letters
by unitors, leaving the power of `U` of the word's count. -/
noncomputable def normIso [Category.{v} A] [MonoidalCategory A]
    (U : A) : (n : ℕ) → (w : Fin n → Bool) →
    (wordPow U (𝟙_ A) n w ≅ tensorPow A U (popCount w))
  | 0, w => eqToIso (congrArg (tensorPow A U) (popCount_nil w).symm)
  | n + 1, w =>
      whiskerRightIso (normIso U n (w ∘ Fin.castSucc))
          (bif w (Fin.last n) then U else 𝟙_ A) ≪≫
        tailIso U (popCount (w ∘ Fin.castSucc)) (w (Fin.last n)) ≪≫
        eqToIso (congrArg (tensorPow A U) (popCount_succ w).symm)

end Norm
end RS
end
