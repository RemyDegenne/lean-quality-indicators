@[expose] public section

open Function Set List

section

variable {B : Type*} (M : CoxeterMatrix B)

/-- A Coxeter system `CoxeterSystem M W` is a structure recording the isomorphism between
a group `W` and the Coxeter group associated to a Coxeter matrix `M`. -/
@[ext]
structure CoxeterSystem (W : Type*) [Group W] where
  /-- The isomorphism between `W` and the Coxeter group associated to `M`. -/
  mulEquiv : W ≃* M.Group

end
end
