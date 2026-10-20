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

namespace IsImage

variable (f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The trivial factorisation of a monomorphism satisfies the universal property. -/
@[simps]
def self [Mono f] : IsImage (MonoFactorisation.self f) where lift F' := F'.e

end IsImage
end CategoryTheory.Limits
end
end
