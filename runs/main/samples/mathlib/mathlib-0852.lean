@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {S}

variable (S)

variable (S₁ S₂)

variable {S₁ S₂}

variable {S}

variable (S)

variable (C)

section

variable {C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

variable {S}

@[reassoc (attr := simp)]
lemma RightHomologyData.opcyclesIso_inv_comp_descOpcycles :
    h.opcyclesIso.inv ≫ S.descOpcycles k hk = h.descQ k hk := by
  simp only [← cancel_epi h.p, p_comp_opcyclesIso_inv_assoc, p_descOpcycles, p_descQ]

end
end ShortComplex
end CategoryTheory
end
