@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]

namespace Pi

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
def eval (i : I) : (∀ i, C i) ⥤ C i where
  obj f := f i
  map α := α i

end Pi
end CategoryTheory
end
