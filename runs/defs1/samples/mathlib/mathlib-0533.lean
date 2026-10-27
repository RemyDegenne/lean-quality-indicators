@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C]

section

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {K L M}

variable (K L M)

/-- The canonical isomorphism `K.op.extend e.op ≅ (K.extend e).op`. -/
noncomputable def extendOpIso : K.op.extend e.op ≅ (K.extend e).op :=
  Hom.isoOfComponents (fun _ ↦ extend.XOpIso _ _) (fun _ _ _ ↦
    extend.XOpIso_hom_d_op _ _ _)

end
end HomologicalComplex
end
