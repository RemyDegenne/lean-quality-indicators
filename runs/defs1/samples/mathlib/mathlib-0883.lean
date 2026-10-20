@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

universe u

namespace TannakaDuality

namespace FiniteGroup

variable {k G : Type u} [CommRing k] [Group G]

section definitions

/-- The representation on `G → k` induced by multiplication on the right in `G`. -/
def rightRegular : Representation k G (G → k) where
  toFun s :=
  { toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

end definitions
end FiniteGroup
end TannakaDuality
end
end
