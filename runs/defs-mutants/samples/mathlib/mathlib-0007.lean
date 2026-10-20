@[expose] public section

open Set

section SaddlePoint

variable {E F : Type*} {β : Type*}

variable (X : Set E) (Y : Set F) (f : E → F → β)

/-- The pair `(a, b)` is a saddle point of `f` on `X × Y`
if `f a y ≤ f x b` for all `x ∈ X` and all `y` in `Y`.

Note: we do not require that `a ∈ X` and `b ∈ Y`. -/
def IsSaddlePointOn [Preorder β] (a : E) (b : F) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, f x b ≤ f a y

end SaddlePoint
end
