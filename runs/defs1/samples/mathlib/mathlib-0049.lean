@[expose] public section

universe u v v'

open Cardinal Submodule Module Function

variable {K : Type u} {V : Type v}

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Basis

variable {ι : Type*} [Fintype ι]

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def basisOfLinearIndependentOfCardEqFinrank'
    [FiniteDimensional K V] (b : ι → V) (hb : LinearIndependent K b)
    (hι : Fintype.card ι = finrank K V) : Basis ι K V :=
  .mk hb (hb.span_eq_top_of_card_eq_finrank' hι).ge

end Basis
end DivisionRing
end
