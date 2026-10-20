public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

theorem isZero_X_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {n : ℤ} (hn : n ∉ Finset.Icc a b) : IsZero (K.X n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isStrictlyGE a n h
  · exact K.isZero_of_isStrictlyLE b n (by omega)

end HomologicalComplex
end
