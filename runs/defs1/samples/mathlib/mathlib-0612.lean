@[expose] public section

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

section

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

/-- The canonical map `K ⟶ K.truncGE n` for `K : CochainComplex C ℤ`. -/
noncomputable def πTruncGE (n : ℤ) : K ⟶ K.truncGE n :=
  HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

end
end HasZeroMorphisms
end CochainComplex
end
