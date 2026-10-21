namespace OAI

namespace Superstring.Hierarchical

namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

@[simp] theorem translate_last (D : Layer V A p) (δ x : ℤ) :
    (D.translate δ).last x = D.last (x - δ) + δ := rfl

end Layer
end Superstring.Hierarchical
end OAI
