set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Embeddings

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

def finEmbedN : GL ι (FiniteAdeleRing R K) →* GL ι (AdeleRing R K) where
  toFun g :=
    { val := finMatN ι R K g
      inv := finMatN ι R K ((g⁻¹ : GL ι (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMatN_mul, Units.mul_inv, finMatN_one]
      inv_val := by rw [← finMatN_mul, Units.inv_mul, finMatN_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMatN_one ι R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMatN_mul ι R K _ _)

end Embeddings
end LanglandsTunnell.CubicInduction
end
