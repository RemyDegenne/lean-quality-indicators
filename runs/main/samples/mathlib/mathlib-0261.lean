@[expose] public section

@[inherit_doc]
notation "ℝ" => Real

namespace Real

open CauSeq CauSeq.Completion

variable {x : ℝ}

@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _

end Real
end
