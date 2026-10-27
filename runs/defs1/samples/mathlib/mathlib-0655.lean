@[expose] public section

noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : X ⟶ Y)

attribute [instance] MonoFactorisation.m_mono

variable {f}

variable (f)

section

variable [HasImage f]

variable {f}

/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the
image. -/
def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  (Image.isImage f).lift F'

end
end CategoryTheory.Limits
end
end
