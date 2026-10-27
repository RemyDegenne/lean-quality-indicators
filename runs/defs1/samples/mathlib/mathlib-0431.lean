@[expose] public section

variable (α : Type*)

open GenContFract

variable {α}

/-- A generalized continued fraction is a *simple continued fraction* if all partial numerators are
equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
-/
def GenContFract.IsSimpContFract (g : GenContFract α)
    [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1

end
