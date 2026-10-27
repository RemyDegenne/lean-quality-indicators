@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

section Preadditive

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable {S}

variable (S)

variable {S}

variable (S)

namespace Splitting

variable {S}

set_option backward.defeqAttrib.useBackward true in
/-- The homology data on a short complex equipped with a splitting. -/
@[simps]
noncomputable def homologyData [HasZeroObject C] (s : S.Splitting) : S.HomologyData where
  left := s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

end Splitting
end Preadditive
end ShortComplex
end CategoryTheory
end
