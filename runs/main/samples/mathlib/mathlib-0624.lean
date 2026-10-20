public section

open CategoryTheory

open CategoryTheory

universe u v w

namespace Condensed

variable {C : Type w} [Category.{v} C]

@[ext]
lemma hom_ext {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.hom.app S = g.hom.app S) :
    f = g := by
  ext
  exact h _

end Condensed
end
