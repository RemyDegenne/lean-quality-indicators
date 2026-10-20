@[expose] public section

namespace List

namespace Vector

variable {α β σ φ : Type*} {n : ℕ} {x : α} {s : σ} (xs : Vector α n)

section Induction

/-- Define `C v` by *reverse* case analysis, i.e. by handling the cases `nil` and `xs.snoc x`
separately -/
@[elab_as_elim]
def revCasesOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C (xs.snoc x)) :
    C v :=
  revInductionOn v nil fun xs x _ => snoc xs x

end Induction
end Vector
end List
end
