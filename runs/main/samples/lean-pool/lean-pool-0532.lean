@[expose] public section

namespace RS

@[simp] theorem interfaceStepOrderIso_apply (s t u : ℕ)
    (x : {x : Fin (s + t + 1) ⊕ Fin (t + 1 + u) //
        x ≠ Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
        x ≠ Sum.inr ⟨t, by omega⟩}) :
    interfaceStepOrderIso s t u x = interfaceStepEquiv s t u x := rfl

end RS
end
