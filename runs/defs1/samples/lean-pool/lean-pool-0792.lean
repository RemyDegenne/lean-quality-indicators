@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-- **The letterwise congruence map** between word powers on the
same word: the fold of `α` on the `true` letters and `β` on the
`false` ones, by the recursion of `wordPow`. -/
noncomputable def wordCongrMap
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {U' : A} {V' : A}
    (α : U' ⟶ U) (β : V' ⟶ V) :
    (n : ℕ) → (w : Fin n → Bool) →
      (wordPow U' V' n w ⟶ wordPow U V n w)
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, w =>
      wordCongrMap α β n (w ∘ Fin.castSucc) ⊗ₘ
        letterCongr α β (w (Fin.last n))

end RS
end
