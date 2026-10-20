public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] {X Y : C} {a b m n : ℤ}

/-- **The splitting of an object killed by a product of coprime integers.** Let `X` satisfy
`(m * n) • 𝟙 X = 0`, where `a * m + b * n = 1`, and let `c₁` and `c₂` be limit kernel forks of
`m • 𝟙 X` and `n • 𝟙 X`. This is the binary bicone with vertex `X` whose inclusions are the kernel
inclusions `c₁.ι` and `c₂.ι`, and whose projections are the factorisations of `(b * n) • 𝟙 X`
through `c₁` and of `(a * m) • 𝟙 X` through `c₂`. It is a bilimit
(`BinaryBicone.isBilimitOfCoprimeKernelForks`). -/
-- Reducible so that the vertex is `X` and the inclusions are `c₁.ι` and `c₂.ι` up to reducible
-- unfolding: lemmas about the bicone are then stated, and rewrite, through `X`.
@[simps pt inl inr]
noncomputable abbrev BinaryBicone.ofCoprimeKernelForks (hab : a * m + b * n = 1)
    (hX : (m * n) • 𝟙 X = 0) {c₁ : KernelFork (m • 𝟙 X)} (hc₁ : IsLimit c₁)
    {c₂ : KernelFork (n • 𝟙 X)} (hc₂ : IsLimit c₂) : BinaryBicone c₁.pt c₂.pt where
  pt := X
  fst := (KernelFork.IsLimit.lift' hc₁ ((b * n) • 𝟙 X) (by
    simp only [Preadditive.zsmul_comp, Category.id_comp]
    linear_combination (norm := module) b • hX)).1
  snd := (KernelFork.IsLimit.lift' hc₂ ((a * m) • 𝟙 X) (by
    simp only [Preadditive.zsmul_comp, Category.id_comp]
    linear_combination (norm := module) a • hX)).1
  inl := c₁.ι
  inr := c₂.ι
  inl_fst := by
    refine Fork.IsLimit.hom_ext hc₁ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₁ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, Category.id_comp]
    linear_combination (norm := module) hab • c₁.ι - a • zsmul_ι_eq_zero c₁
  inl_snd := by
    refine Fork.IsLimit.hom_ext hc₂ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₂ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, zero_comp]
    linear_combination (norm := module) a • zsmul_ι_eq_zero c₁
  inr_fst := by
    refine Fork.IsLimit.hom_ext hc₁ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₁ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, zero_comp]
    linear_combination (norm := module) b • zsmul_ι_eq_zero c₂
  inr_snd := by
    refine Fork.IsLimit.hom_ext hc₂ ?_
    simp only [Category.assoc, (KernelFork.IsLimit.lift' hc₂ _ _).2, Preadditive.comp_zsmul,
      Category.comp_id, Category.id_comp]
    linear_combination (norm := module) hab • c₂.ι - b • zsmul_ι_eq_zero c₂

end CategoryTheory.Limits
end
