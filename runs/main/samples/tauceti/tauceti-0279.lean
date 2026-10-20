public section

open CategoryTheory Limits

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Complex

variable (n : ℕ) (K : CochainComplex C ℤ) (k : ℤ) [HasCompression n K]

@[reassoc (attr := simp)]
lemma ιCompression_compressionShiftXIso_hom (i : ℤ) (r : ZMod n)
    (hi : (i : ZMod n) = r) :
    ιCompression n (K⟦k⟧) i r hi ≫ (compressionShiftXIso n K k r).hom =
      (CochainComplex.shiftFunctorObjXIso K k i (i + k) rfl).hom ≫
        ιCompression n K (i + k) (r + k) (by simp [hi]) := by
  simp [compressionShiftXIso]

end Complex
end TauCeti.PeriodicComplex
end
