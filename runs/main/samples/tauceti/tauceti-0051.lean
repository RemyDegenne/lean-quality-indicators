public section

open AlgebraicGeometry CategoryTheory

open scoped CategoryTheory.MonObj

namespace TauCeti

namespace SpecialLinear

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

section SchemePoints

variable {R} (A : Type u) [CommRing A] [Algebra R A]

-- Not `@[simp]`: `simp` normalizes the point before this equation can apply, so it never fires,
-- even on its own statement; use it by name.
lemma groupSchemePointMulEquiv_apply_left
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (groupSchemePointMulEquiv n A f).left =
      Spec.map (CommRingCat.ofHom f.ofConv) ≫
        eqToHom (groupScheme_X_left R n).symm := by
  simpa only [groupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (coordinateHopfAlgebra R n) A (groupScheme_def R n)
        (groupScheme_X_left R n) f

end SchemePoints
end SpecialLinear
end TauCeti
end
