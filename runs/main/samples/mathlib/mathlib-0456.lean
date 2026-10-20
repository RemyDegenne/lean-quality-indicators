@[expose] public section

universe v u

namespace CategoryTheory

open Limits Category Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace kernelCokernelCompSequence

@[reassoc (attr := simp)]
lemma φ_snd : φ f g ≫ biprod.snd = biprod.snd ≫ g := by
  dsimp [φ]
  aesop

end kernelCokernelCompSequence
end CategoryTheory
end
