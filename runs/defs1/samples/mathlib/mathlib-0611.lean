@[expose] public section

variable {D C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C]

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def ValuedCSP.Instance.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : C :=
  (I.map (·.evalSolution x)).sum

end
