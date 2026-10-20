@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section Nonzero

variable {A : Type u}

theorem tensorPow_id_ne_zero
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    (hone : ¬ Limits.IsZero (𝟙_ A))
    {U : A} (hUU : U ⊗ U ≅ 𝟙_ A) :
    ∀ k : ℕ, 𝟙 (tensorPow A U k) ≠
      (0 : tensorPow A U k ⟶ tensorPow A U k) := by
  intro k
  induction k with
  | zero =>
    intro h
    exact hone ((Limits.IsZero.iff_id_eq_zero (𝟙_ A)).mpr h)
  | succ k ih =>
    intro h
    have h1 : 𝟙 (tensorPow A U (k + 1) ⊗ U) = 0 := by
      rw [← MonoidalCategory.id_whiskerRight, h,
        MonoidalPreadditive.zero_whiskerRight]
    exact ih (id_zero_transfer
      ((α_ (tensorPow A U k) U U) ≪≫
        whiskerLeftIso (tensorPow A U k) hUU ≪≫
        ρ_ (tensorPow A U k)) h1)

end Nonzero
end RS
end
