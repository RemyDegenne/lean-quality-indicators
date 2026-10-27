@[expose] public section

variable {G P : Type*}

namespace Set

section SMul

variable [SMul G P] {s s₁ s₂ : Set G} {t t₁ t₂ : Set P} {a : P} {x : G × P}

/-- `smulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that scalar multiply to `a`. -/
@[to_additive /-- `vaddAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that vector-add to `a`. -/]
def smulAntidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a }

end SMul
end Set
end
