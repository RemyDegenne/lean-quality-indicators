public section

open scoped DirectSum

namespace TauCeti

universe u v w

namespace GradedLinearQuiver

variable (R : Type w) [CommRing R] {C : Type u}

variable {F : (X Y : C) → CategoryTheory.GradedObject ℤ (ModuleCat.{v} R)}

variable [GradedLinearQuiver R C] {X Y : C}

/-- Record a morphism of degree `n` as a morphism of degree `k`, along an equation `h : n = k` of
degrees.  The underlying morphism is unchanged. -/
def grHomReindex {n k : ℤ} (h : n = k) (f : grHom R X Y n) : grHom R X Y k :=
  ⟨f, by rw [← h]; exact f.property⟩

end GradedLinearQuiver
end TauCeti
end
