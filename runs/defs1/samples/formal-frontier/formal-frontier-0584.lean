@[expose] public section

universe u v w w₁

namespace CoalgEquiv

variable {K : Type u} {C : Type v} {C' : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

/-- Transport subcoalgebras along an ambient coalgebra equivalence, by taking the image
under the equivalence and taking the image under its inverse for the inverse operation. -/
noncomputable def subcoalgebraCongr (e : C ≃ₗc[K] C') :
    Subcoalgebra K C ≃ Subcoalgebra K C' := by
  refine
    { toFun := Subcoalgebra.map e.toCoalgHom
      invFun := Subcoalgebra.map e.symm.toCoalgHom
      left_inv := ?_
      right_inv := ?_ }
  · intro D
    rw [← Subcoalgebra.map_comp]
    have h : e.symm.toCoalgHom.comp e.toCoalgHom = CoalgHom.id K C :=
      CoalgHom.ext fun x => e.symm_apply_apply x
    rw [h, Subcoalgebra.map_id]
  · intro D
    rw [← Subcoalgebra.map_comp]
    have h : e.toCoalgHom.comp e.symm.toCoalgHom = CoalgHom.id K C' :=
      CoalgHom.ext fun x => e.apply_symm_apply x
    rw [h, Subcoalgebra.map_id]

end CoalgEquiv
end
