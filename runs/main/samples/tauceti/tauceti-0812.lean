public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

variable {G : Type*} [Group G] (φ : G →* (F ≃ₐ[k] F))

@[simp] theorem placePermHomOfInvariant_apply {S : Finset (Place k F)}
    (hS : ∀ (g : G) (P : Place k F), P ∈ S → φ g • P ∈ S) (g : G) (P : S) :
    ((placePermHomOfInvariant φ hS g) P).1 = φ g • P.1 := (rfl)

end TauCeti
end
