public section

open CategoryTheory Limits

universe v u

namespace TauCeti

namespace PeriodicComplex

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] (n : ℕ)

variable (K L M : CochainComplex C ℤ) [HasCompression n K] [HasCompression n L]
  [HasCompression n M]

@[reassoc]
lemma ιCompression_d (i j : ℤ) (hij : i + 1 = j) (r s : ZMod n) (hi : (i : ZMod n) = r)
    (hj : (j : ZMod n) = s) :
    ιCompression n K i r hi ≫ (compression n K).d r s = K.d i j ≫ ιCompression n K j s hj := by
  subst hij
  simp [compression, ιCompression, compressionDifferential,
    GradedObject.ιMapObjOrZero_eq _ _ _ _ hj]

end HasZeroMorphisms
end PeriodicComplex
end TauCeti
end
