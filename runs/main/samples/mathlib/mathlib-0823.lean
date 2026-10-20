@[expose] public section

universe w w' u u' v v'

open CategoryTheory

open scoped MonoidAlgebra

namespace Rep

noncomputable section

section semiring

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G] {X Y : Type w} [AddCommGroup X]
  [AddCommGroup Y] [Module k X] [Module k Y] {ρ : Representation k G X} {σ : Representation k G Y}
  (A B C : Rep.{w} k G)

attribute [instance] hV1

attribute [instance 1100] hV2

variable {Z : Type w} [AddCommGroup Z] [Module k Z] {τ : Representation k G Z}

@[simp]
lemma ofHom_comp (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
  ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

end semiring
end
end Rep
end
