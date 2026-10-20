@[expose] public section

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

scoped macro:max K:term "⟮" xs:term,* "⟯" : term => do ``(adjoin $K $(← mkInsertTerm xs.getElems))

section AdjoinSimple

variable (α : E)

variable {F} {α}

variable {A B C : Type*} [Field A] [Field B] [Field C] [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] (b : B)

/-- Ring homomorphism between `A⟮b⟯` and `A⟮↑b⟯`. -/
def RingHom.adjoinAlgebraMap : A⟮b⟯ →+* A⟮((algebraMap B C) b)⟯ :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp (IntermediateField.val A⟮b⟯)) _
    (fun x ↦ by
      rw [show (algebraMap B C) b = (Algebra.ofId B C).restrictScalars A b by rfl,
        ← Set.image_singleton, ← IntermediateField.adjoin_map A {b}]
      use x
      simp)

end AdjoinSimple
end AdjoinDef
end IntermediateField
end
