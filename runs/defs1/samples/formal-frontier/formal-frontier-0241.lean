@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M]

namespace Subcomodule

variable {X : RightComodule R C M}

/-- The zero submodule with its zero subtype coaction. -/
def bot (X : RightComodule R C M) : X.Subcomodule where
  toSubmodule := ⊥
  comodule := {
    coaction := 0
    coassoc := by ext m; simp
    counit_comp := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      simp [hm] }
  subtype_colinear := by
    ext m
    have hm : m = 0 := Subsingleton.elim _ _
    simp [hm]

end Subcomodule
end RightComodule
end Coalgebra
end
