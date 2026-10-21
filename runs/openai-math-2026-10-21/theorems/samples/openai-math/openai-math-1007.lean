namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

open MeasureTheory

theorem subdivision_locallyFinite (G : BondGraph V E) (hloc : LocallyFinite G) :
    LocallyFinite (subdivision G) := by
  classical
  intro z
  cases z with
  | inl x =>
    apply Set.Finite.of_finite_image (f := fun e : SubdivisionEdge G => e.val.1)
    · apply (hloc x).subset
      rintro e ⟨⟨⟨f,y⟩,hy⟩,hz,rfl⟩
      have he : x = y := by simpa [subdivision] using hz
      simpa [he] using hy
    · intro e he f hf hef
      apply Subtype.ext
      apply Prod.ext hef
      have hx : x = e.val.2 := by simpa [subdivision] using he
      have hy : x = f.val.2 := by simpa [subdivision] using hf
      exact hx.symm.trans hy
  | inr e =>
    apply Set.Finite.of_finite_image (f := fun f : SubdivisionEdge G => f.val.2)
    · apply (Sym2.toFinset (G e)).finite_toSet.subset
      rintro x ⟨⟨⟨f,y⟩,hy⟩,hz,rfl⟩
      have he : e = f := by simpa [subdivision] using hz
      simpa [he] using hy
    · intro f hf g hg hfg
      apply Subtype.ext
      apply Prod.ext _ hfg
      have h₁ : e = f.val.1 := by simpa [subdivision] using hf
      have h₂ : e = g.val.1 := by simpa [subdivision] using hg
      exact h₁.symm.trans h₂

end Percolation
end OAI
