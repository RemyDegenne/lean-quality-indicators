@[expose] public section

universe u w w'

open CategoryTheory

namespace KTheory

variable (R : Type u) [Ring R]

namespace K0

/-- The opposite-ring additive equivalence on K₀ obtained by localizing the
finite-projective class duality. This is the group-completion duality of
Weibel's *The K-book*, Chapter II. -/
noncomputable def dualEquiv : K0 R ≃+ K0 Rᵐᵒᵖ :=
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))).addEquivOfAddEquiv
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass Rᵐᵒᵖ)))
    (j := ProjectiveClass.dualEquiv R) (by
      rw [← AddMonoidHom.mrange_eq_map]
      exact AddMonoidHom.mrange_eq_top_of_surjective _
        (ProjectiveClass.dualEquiv R).surjective)

end K0
end KTheory
end
