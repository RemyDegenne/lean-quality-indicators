@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable {C c}

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

section

variable [K.HasHomology i]

/-- The homology class map from cycles to the homology of a homological complex. -/
noncomputable def homologyπ : K.cycles i ⟶ K.homology i := (K.sc i).homologyπ

end
end HomologicalComplex
end
