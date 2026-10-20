@[expose] public section

open Set OrderDual

variable {ι α β : Type*}

variable {P Q : α → Prop} {a x y : α}

section LE

variable [LE α]

@[to_dual (attr := simp)]
theorem minimal_subtype {x : Subtype Q} :
    Minimal (fun x ↦ P x.1) x ↔ Minimal (P ⊓ Q) x := by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

end LE
end
