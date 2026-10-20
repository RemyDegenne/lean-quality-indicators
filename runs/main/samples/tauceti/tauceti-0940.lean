public section

noncomputable section

open CategoryTheory

universe u v w v₁ v₂ v₃

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R]

variable {X : TopCat.{v}}

@[simp]
theorem basepointChangeEquiv_apply (L : LocalCoefficientSystem.{u, v, w} R X) {x y : X}
    (p : Path x y) (a : L.obj (FundamentalGroupoid.mk x)) :
    basepointChangeEquiv L p a = transport L ⟦p⟧ a :=
  rfl

end LocalCoefficientSystem
end TauCeti
end
end
